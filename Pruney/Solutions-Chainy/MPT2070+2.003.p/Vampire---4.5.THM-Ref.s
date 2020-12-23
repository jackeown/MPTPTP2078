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
% DateTime   : Thu Dec  3 13:23:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 (6230 expanded)
%              Number of leaves         :   23 (2336 expanded)
%              Depth                    :   15
%              Number of atoms          : 1089 (117057 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f123,f127,f155,f176])).

fof(f176,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f174,f171])).

fof(f171,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ( r1_waybel_7(X0,sK7(X0,X1,X2),X2)
                    & r2_hidden(X1,sK7(X0,X1,X2))
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(sK7(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(sK7(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X0,sK7(X0,X1,X2),X2)
        & r2_hidden(X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK7(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

fof(f159,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f122,f87,f92,f97,f38,f117,f112,f107,f102,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X3)
      | ~ r2_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
                    & r2_hidden(X1,sK6(X0,X1,X2))
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(sK6(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X4) )
     => ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r2_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r2_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).

fof(f102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl8_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f107,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_7
  <=> v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f112,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_8
  <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f117,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_9
  <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f97,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f87,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_3
  <=> r2_waybel_7(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f122,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( ~ r2_hidden(sK3,sK1)
        & r2_waybel_7(sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & r2_hidden(sK1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(sK2) )
      | ~ v4_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK1)
              | ~ r2_waybel_7(sK0,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          | ~ r2_hidden(sK1,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(sK0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,X1)
                  & r2_waybel_7(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(X1,sK0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X1)
                  | ~ r2_waybel_7(sK0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              | ~ r2_hidden(X1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              | v1_xboole_0(X4) )
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,sK1)
                & r2_waybel_7(sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & r2_hidden(sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
            & ~ v1_xboole_0(X2) )
        | ~ v4_pre_topc(sK1,sK0) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,sK1)
                | ~ r2_waybel_7(sK0,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            | ~ r2_hidden(sK1,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            | v1_xboole_0(X4) )
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,sK1)
            & r2_waybel_7(sK0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_hidden(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,sK1)
          & r2_waybel_7(sK0,sK2,X3)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & r2_hidden(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK1)
        & r2_waybel_7(sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(sK3,sK1)
      & r2_waybel_7(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).

fof(f92,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f174,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f82,f77,f92,f38,f167,f172,f173,f169,f170,f168,f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( v1_xboole_0(X4)
      | ~ r1_waybel_7(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_hidden(X1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | r2_hidden(X5,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r1_waybel_7(X0,sK4(X0,X1),sK5(X0,X1))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & r2_hidden(X1,sK4(X0,X1))
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(sK4(X0,X1)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_waybel_7(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_hidden(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_waybel_7(X0,sK4(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_hidden(X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_waybel_7(X0,sK4(X0,X1),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r1_waybel_7(X0,sK4(X0,X1),sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_waybel_7(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X2)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow19)).

fof(f168,plain,
    ( v1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(sK7(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,
    ( v13_waybel_0(sK7(sK0,sK1,sK3),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f169,plain,
    ( v2_waybel_0(sK7(sK0,sK1,sK3),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f173,plain,
    ( r1_waybel_7(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,sK7(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f172,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1,sK3))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f167,plain,
    ( ~ v1_xboole_0(sK7(sK0,sK1,sK3))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v1_xboole_0(sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f82,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f155,plain,
    ( spl8_1
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f153,f143])).

fof(f143,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f138,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f129,f128,f131,f135,f132,f133,f134,f136,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X3)
      | ~ r1_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f136,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f134,plain,
    ( v1_subset_1(sK4(sK0,sK1),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,
    ( v13_waybel_0(sK4(sK0,sK1),k3_yellow_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f132,plain,
    ( v2_waybel_0(sK4(sK0,sK1),k3_yellow_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f135,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1),sK5(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_waybel_7(X0,sK4(X0,X1),sK5(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(sK4(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f131,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f153,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl8_1
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f130,f131,f139,f144,f142,f141,f140,f145,f126])).

fof(f126,plain,
    ( ! [X4,X5] :
        ( v1_xboole_0(X4)
        | r2_hidden(X5,sK1)
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,X4,X5) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_11
  <=> ! [X5,X4] :
        ( r2_hidden(X5,sK1)
        | v1_xboole_0(X4)
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f145,plain,
    ( r2_waybel_7(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK5(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,
    ( v2_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,
    ( v13_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,
    ( v3_waybel_7(sK6(sK0,sK1,sK5(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f144,plain,
    ( r2_hidden(sK1,sK6(sK0,sK1,sK5(sK0,sK1)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f139,plain,
    ( ~ v1_xboole_0(sK6(sK0,sK1,sK5(sK0,sK1)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v1_xboole_0(sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f130,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f127,plain,
    ( spl8_1
    | spl8_11 ),
    inference(avatar_split_clause,[],[f39,f125,f76])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_waybel_7(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f123,plain,
    ( ~ spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f40,f120,f76])).

fof(f40,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f118,plain,
    ( ~ spl8_1
    | spl8_9 ),
    inference(avatar_split_clause,[],[f41,f115,f76])).

fof(f41,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f113,plain,
    ( ~ spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f42,f110,f76])).

fof(f42,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( ~ spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f43,f105,f76])).

fof(f43,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f44,f100,f76])).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f45,f95,f76])).

fof(f45,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f46,f90,f76])).

fof(f46,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f47,f85,f76])).

fof(f47,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f48,f80,f76])).

fof(f48,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (9680)WARNING: option uwaf not known.
% 0.21/0.48  % (9680)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.49  % (9683)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (9675)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (9682)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (9675)Refutation not found, incomplete strategy% (9675)------------------------------
% 0.21/0.50  % (9675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9675)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9675)Memory used [KB]: 1023
% 0.21/0.50  % (9675)Time elapsed: 0.063 s
% 0.21/0.50  % (9675)------------------------------
% 0.21/0.50  % (9675)------------------------------
% 0.21/0.50  % (9684)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.50  % (9684)Refutation not found, incomplete strategy% (9684)------------------------------
% 0.21/0.50  % (9684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9684)Memory used [KB]: 5373
% 0.21/0.50  % (9684)Time elapsed: 0.004 s
% 0.21/0.50  % (9684)------------------------------
% 0.21/0.50  % (9684)------------------------------
% 0.21/0.50  % (9673)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.51  % (9676)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.51  % (9690)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.51  % (9673)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f123,f127,f155,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f174,f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    m1_subset_1(sK7(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & ((r1_waybel_7(X0,sK7(X0,X1,X2),X2) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK7(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK7(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (r1_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X4)) => (r1_waybel_7(X0,sK7(X0,X1,X2),X2) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK7(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK7(X0,X1,X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & (? [X4] : (r1_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & (? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f122,f87,f92,f97,f38,f117,f112,f107,f102,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X3) | ~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & ((r2_waybel_7(X0,sK6(X0,X1,X2),X2) & r2_hidden(X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) => (r2_waybel_7(X0,sK6(X0,X1,X2),X2) & r2_hidden(X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl8_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl8_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~spl8_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl8_7 <=> v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl8_8 <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~spl8_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl8_9 <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    r2_hidden(sK1,sK2) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl8_5 <=> r2_hidden(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK2,sK3) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl8_3 <=> r2_waybel_7(sK0,sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl8_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl8_10 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ((((~r2_hidden(sK3,sK1) & r2_waybel_7(sK0,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(sK2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r2_hidden(sK3,sK1) & r2_waybel_7(sK0,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl8_4 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~m1_subset_1(sK7(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f82,f77,f92,f38,f167,f172,f173,f169,f170,f168,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X4,X0,X5,X1] : (v1_xboole_0(X4) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | r2_hidden(X5,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_waybel_7(X0,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & r2_hidden(X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4(X0,X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_waybel_7(X0,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow19)).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    v1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_subset_1(sK7(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    v13_waybel_0(sK7(sK0,sK1,sK3),k3_yellow_1(k2_struct_0(sK0))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v13_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    v2_waybel_0(sK7(sK0,sK1,sK3),k3_yellow_1(k2_struct_0(sK0))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_waybel_0(sK7(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    r1_waybel_7(sK0,sK7(sK0,sK1,sK3),sK3) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_waybel_7(X0,sK7(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    r2_hidden(sK1,sK7(sK0,sK1,sK3)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,sK7(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~v1_xboole_0(sK7(sK0,sK1,sK3)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f92,f38,f159,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v1_xboole_0(sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    v4_pre_topc(sK1,sK0) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl8_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK1) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl8_2 <=> r2_hidden(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl8_1 | ~spl8_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    $false | (spl8_1 | ~spl8_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f129,f128,f131,f135,f132,f133,f134,f136,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X3) | ~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~v4_pre_topc(sK1,sK0) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    v1_subset_1(sK4(sK0,sK1),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    v13_waybel_0(sK4(sK0,sK1),k3_yellow_1(k2_struct_0(sK0))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0))) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    v2_waybel_0(sK4(sK0,sK1),k3_yellow_1(k2_struct_0(sK0))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X0))) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    r1_waybel_7(sK0,sK4(sK0,sK1),sK5(sK0,sK1)) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_waybel_7(X0,sK4(X0,X1),sK5(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~v1_xboole_0(sK4(sK0,sK1)) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v1_xboole_0(sK4(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    r2_hidden(sK1,sK4(sK0,sK1)) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X1,sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | (spl8_1 | ~spl8_11)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f130,f131,f139,f144,f142,f141,f140,f145,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X4,X5] : (v1_xboole_0(X4) | r2_hidden(X5,sK1) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,X4,X5)) ) | ~spl8_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl8_11 <=> ! [X5,X4] : (r2_hidden(X5,sK1) | v1_xboole_0(X4) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,X4,X5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK5(sK0,sK1)) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_waybel_7(X0,sK6(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    v2_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    v13_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    v3_waybel_7(sK6(sK0,sK1,sK5(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    r2_hidden(sK1,sK6(sK0,sK1,sK5(sK0,sK1))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~v1_xboole_0(sK6(sK0,sK1,sK5(sK0,sK1))) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f131,f138,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v1_xboole_0(sK6(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~r2_hidden(sK5(sK0,sK1),sK1) | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f36,f37,f78,f38,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    spl8_1 | spl8_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f125,f76])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X4,X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4) | v4_pre_topc(sK1,sK0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f120,f76])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~spl8_1 | spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f115,f76])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~spl8_1 | spl8_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f110,f76])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~spl8_1 | spl8_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f105,f76])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~spl8_1 | spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f100,f76])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~spl8_1 | spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f95,f76])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r2_hidden(sK1,sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~spl8_1 | spl8_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f90,f76])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~spl8_1 | spl8_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f85,f76])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK2,sK3) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f80,f76])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (9673)------------------------------
% 0.21/0.51  % (9673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9673)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (9673)Memory used [KB]: 10106
% 0.21/0.51  % (9673)Time elapsed: 0.092 s
% 0.21/0.51  % (9673)------------------------------
% 0.21/0.51  % (9673)------------------------------
% 0.21/0.51  % (9674)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.52  % (9688)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (9669)Success in time 0.151 s
%------------------------------------------------------------------------------
