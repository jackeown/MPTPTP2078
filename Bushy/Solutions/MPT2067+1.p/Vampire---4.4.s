%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t27_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 9.11s
% Output     : Refutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :  195 (1628 expanded)
%              Number of leaves         :   38 ( 414 expanded)
%              Depth                    :   12
%              Number of atoms          : 1027 (13260 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f269,f292,f319,f331,f369,f402,f420,f454,f605,f660,f864,f1889,f2941,f2956,f2994,f3157,f4218,f5164,f51621,f51664])).

fof(f51664,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_862 ),
    inference(avatar_contradiction_clause,[],[f51659])).

fof(f51659,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_862 ),
    inference(unit_resulting_resolution,[],[f268,f867,f51643,f144])).

fof(f144,plain,(
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
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t2_subset)).

fof(f51643,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_862 ),
    inference(forward_demodulation,[],[f51640,f895])).

fof(f895,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)) = sK3
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f122,f204,f268,f368,f330,f401,f419,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t15_yellow19)).

fof(f419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl12_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f401,plain,
    ( v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl12_12
  <=> v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f330,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl12_8
  <=> v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f368,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl12_10
  <=> v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f204,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f124,f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',dt_l1_pre_topc)).

fof(f124,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t27_yellow19)).

fof(f122,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f51640,plain,
    ( ~ r2_hidden(sK1,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14
    | ~ spl12_862 ),
    inference(unit_resulting_resolution,[],[f122,f204,f902,f901,f51634,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t11_yellow19)).

fof(f51634,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK1)
    | ~ spl12_1
    | ~ spl12_6
    | ~ spl12_862 ),
    inference(unit_resulting_resolution,[],[f318,f120,f259,f121,f51620])).

fof(f51620,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK0,sK3,X1)
        | r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0) )
    | ~ spl12_862 ),
    inference(avatar_component_clause,[],[f51619])).

fof(f51619,plain,
    ( spl12_862
  <=> ! [X1,X0] :
        ( ~ r1_waybel_7(sK0,sK3,X1)
        | r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_862])])).

fof(f121,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f259,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl12_1
  <=> ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f120,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f318,plain,
    ( r1_waybel_7(sK0,sK3,sK2)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl12_6
  <=> r1_waybel_7(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f901,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f122,f204,f268,f211,f368,f330,f212,f419,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',dt_k3_yellow19)).

fof(f212,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f204,f140])).

fof(f140,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',dt_k2_struct_0)).

fof(f211,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f122,f204,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',fc5_struct_0)).

fof(f902,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f122,f204,f268,f211,f368,f330,f212,f419,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',fc4_yellow19)).

fof(f867,plain,
    ( m1_subset_1(sK1,sK3)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f291,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t1_subset)).

fof(f291,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl12_4
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f268,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl12_3
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f51621,plain,
    ( ~ spl12_161
    | spl12_30
    | ~ spl12_311
    | ~ spl12_33
    | spl12_862
    | spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_212
    | ~ spl12_384 ),
    inference(avatar_split_clause,[],[f5181,f5162,f2939,f418,f400,f367,f329,f267,f51619,f599,f4190,f593,f1880])).

fof(f1880,plain,
    ( spl12_161
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_161])])).

fof(f593,plain,
    ( spl12_30
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f4190,plain,
    ( spl12_311
  <=> ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_311])])).

fof(f599,plain,
    ( spl12_33
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f2939,plain,
    ( spl12_212
  <=> ! [X3,X4] :
        ( ~ v2_pre_topc(X3)
        | r3_waybel_9(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X4)
        | ~ r1_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_212])])).

fof(f5162,plain,
    ( spl12_384
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X1)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_384])])).

fof(f5181,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK0,sK3,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_212
    | ~ spl12_384 ),
    inference(forward_demodulation,[],[f5180,f895])).

fof(f5180,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X1)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_212
    | ~ spl12_384 ),
    inference(duplicate_literal_removal,[],[f5179])).

fof(f5179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_212
    | ~ spl12_384 ),
    inference(resolution,[],[f5163,f2940])).

fof(f2940,plain,
    ( ! [X4,X3] :
        ( r3_waybel_9(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X4)
        | ~ v2_pre_topc(X3)
        | ~ r1_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl12_212 ),
    inference(avatar_component_clause,[],[f2939])).

fof(f5163,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X1)
        | r2_hidden(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl12_384 ),
    inference(avatar_component_clause,[],[f5162])).

fof(f5164,plain,
    ( ~ spl12_161
    | spl12_30
    | ~ spl12_311
    | spl12_384
    | ~ spl12_228 ),
    inference(avatar_split_clause,[],[f3173,f3155,f5162,f4190,f593,f1880])).

fof(f3155,plain,
    ( spl12_228
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X2)
        | ~ r1_waybel_0(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X1)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_228])])).

fof(f3173,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X1)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_228 ),
    inference(resolution,[],[f3156,f123])).

fof(f123,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f3156,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X2)
        | ~ r1_waybel_0(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X1)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl12_228 ),
    inference(avatar_component_clause,[],[f3155])).

fof(f4218,plain,
    ( spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14
    | spl12_311 ),
    inference(avatar_contradiction_clause,[],[f4212])).

fof(f4212,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14
    | ~ spl12_311 ),
    inference(unit_resulting_resolution,[],[f204,f122,f268,f211,f368,f330,f212,f419,f4191,f132])).

fof(f4191,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | ~ spl12_311 ),
    inference(avatar_component_clause,[],[f4190])).

fof(f3157,plain,
    ( ~ spl12_209
    | spl12_210
    | spl12_228
    | spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f913,f418,f400,f367,f329,f267,f3155,f2936,f2930])).

fof(f2930,plain,
    ( spl12_209
  <=> ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_209])])).

fof(f2936,plain,
    ( spl12_210
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_210])])).

fof(f913,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ r1_waybel_0(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X1)
        | ~ r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X2)
        | r2_hidden(X2,k2_pre_topc(X0,X1)) )
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(resolution,[],[f898,f158])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ r3_waybel_9(X0,X3,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t23_yellow19)).

fof(f898,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f268,f204,f122,f211,f368,f330,f212,f401,f419,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',fc5_yellow19)).

fof(f2994,plain,
    ( spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_210 ),
    inference(avatar_contradiction_clause,[],[f2985])).

fof(f2985,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_210 ),
    inference(unit_resulting_resolution,[],[f122,f204,f268,f211,f368,f330,f401,f212,f419,f2937,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2937,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl12_210 ),
    inference(avatar_component_clause,[],[f2936])).

fof(f2956,plain,
    ( spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14
    | spl12_209 ),
    inference(avatar_contradiction_clause,[],[f2951])).

fof(f2951,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_14
    | ~ spl12_209 ),
    inference(unit_resulting_resolution,[],[f122,f204,f268,f211,f368,f330,f212,f419,f2931,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f2931,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl12_209 ),
    inference(avatar_component_clause,[],[f2930])).

fof(f2941,plain,
    ( ~ spl12_209
    | spl12_210
    | spl12_212
    | spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f914,f418,f400,f367,f329,f267,f2939,f2936,f2930])).

fof(f914,plain,
    ( ! [X4,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | v2_struct_0(X3)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r1_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X4)
        | r3_waybel_9(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X4) )
    | ~ spl12_3
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(resolution,[],[f898,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',t12_yellow19)).

fof(f1889,plain,(
    spl12_161 ),
    inference(avatar_contradiction_clause,[],[f1886])).

fof(f1886,plain,
    ( $false
    | ~ spl12_161 ),
    inference(unit_resulting_resolution,[],[f124,f1881])).

fof(f1881,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_161 ),
    inference(avatar_component_clause,[],[f1880])).

fof(f864,plain,
    ( ~ spl12_0
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f850])).

fof(f850,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_20 ),
    inference(unit_resulting_resolution,[],[f334,f449,f456,f337,f335,f336,f338,f453])).

fof(f453,plain,
    ( ! [X3] :
        ( ~ r1_waybel_7(sK0,X3,sK2)
        | v1_xboole_0(X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl12_20
  <=> ! [X3] :
        ( v1_xboole_0(X3)
        | ~ r1_waybel_7(sK0,X3,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f338,plain,
    ( m1_subset_1(k2_yellow19(sK0,sK5(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f204,f301,f304,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',dt_k2_yellow19)).

fof(f304,plain,
    ( l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f124,f123,f122,f120,f121,f262,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f262,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl12_0
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f301,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f124,f122,f123,f120,f121,f262,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f336,plain,
    ( v1_subset_1(k2_yellow19(sK0,sK5(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f204,f303,f302,f301,f304,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',fc3_yellow19)).

fof(f302,plain,
    ( v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f124,f122,f123,f120,f121,f262,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f303,plain,
    ( v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f124,f122,f123,f120,f121,f262,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v7_waybel_0(sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f335,plain,
    ( v13_waybel_0(k2_yellow19(sK0,sK5(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f204,f301,f304,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',fc2_yellow19)).

fof(f337,plain,
    ( v2_waybel_0(k2_yellow19(sK0,sK5(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f204,f303,f302,f301,f304,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f456,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,sK5(sK0,sK1,sK2)),sK2)
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f123,f124,f120,f303,f302,f301,f304,f306,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f306,plain,
    ( r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f124,f123,f122,f120,f121,f262,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,sK5(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f449,plain,
    ( r2_hidden(sK1,k2_yellow19(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl12_0 ),
    inference(forward_demodulation,[],[f446,f343])).

fof(f343,plain,
    ( k2_yellow19(sK0,sK5(sK0,sK1,sK2)) = a_2_1_yellow19(sK0,sK5(sK0,sK1,sK2))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f204,f301,f304,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',d3_yellow19)).

fof(f446,plain,
    ( r2_hidden(sK1,a_2_1_yellow19(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f204,f122,f121,f301,f304,f305,f201])).

fof(f201,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_waybel_0(X1,X2,X3)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | r2_hidden(X3,a_2_1_yellow19(X1,X2)) ) ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | ~ r1_waybel_0(X1,X2,X3)
      | r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t27_yellow19.p',fraenkel_a_2_1_yellow19)).

fof(f305,plain,
    ( r1_waybel_0(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f124,f123,f122,f120,f121,f262,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_0(X0,sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f334,plain,
    ( ~ v1_xboole_0(k2_yellow19(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f122,f204,f301,f304,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f660,plain,(
    ~ spl12_30 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f122,f594])).

fof(f594,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f593])).

fof(f605,plain,(
    spl12_33 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl12_33 ),
    inference(unit_resulting_resolution,[],[f123,f600])).

fof(f600,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl12_33 ),
    inference(avatar_component_clause,[],[f599])).

fof(f454,plain,
    ( ~ spl12_1
    | spl12_20 ),
    inference(avatar_split_clause,[],[f112,f452,f258])).

fof(f112,plain,(
    ! [X3] :
      ( v1_xboole_0(X3)
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ r2_hidden(sK1,X3)
      | ~ r1_waybel_7(sK0,X3,sK2)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f420,plain,
    ( spl12_0
    | spl12_14 ),
    inference(avatar_split_clause,[],[f117,f418,f261])).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f402,plain,
    ( spl12_0
    | spl12_12 ),
    inference(avatar_split_clause,[],[f114,f400,f261])).

fof(f114,plain,
    ( v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f369,plain,
    ( spl12_0
    | spl12_10 ),
    inference(avatar_split_clause,[],[f116,f367,f261])).

fof(f116,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f331,plain,
    ( spl12_0
    | spl12_8 ),
    inference(avatar_split_clause,[],[f115,f329,f261])).

fof(f115,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f319,plain,
    ( spl12_0
    | spl12_6 ),
    inference(avatar_split_clause,[],[f119,f317,f261])).

fof(f119,plain,
    ( r1_waybel_7(sK0,sK3,sK2)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f292,plain,
    ( spl12_0
    | spl12_4 ),
    inference(avatar_split_clause,[],[f118,f290,f261])).

fof(f118,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f269,plain,
    ( spl12_0
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f113,f267,f261])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
