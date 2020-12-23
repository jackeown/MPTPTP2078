%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2070+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 (1177 expanded)
%              Number of leaves         :   19 ( 278 expanded)
%              Depth                    :   12
%              Number of atoms          :  430 (9778 expanded)
%              Number of equality atoms :   13 ( 170 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f83,f94,f99,f104,f109,f118,f123,f130,f152,f196,f513])).

fof(f513,plain,
    ( spl6_1
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | spl6_1
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f232,f261,f266,f271,f267,f268,f269,f270,f272,f151])).

fof(f151,plain,
    ( ! [X2,X3] :
        ( ~ r2_waybel_7(sK0,X2,X3)
        | r2_hidden(X3,sK1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_11
  <=> ! [X3,X2] :
        ( v1_xboole_0(X2)
        | r2_hidden(X3,sK1)
        | ~ r2_waybel_7(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f272,plain,
    ( r2_waybel_7(sK0,sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK5(k2_pre_topc(sK0,sK1),sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_waybel_7(X0,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f231,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f227,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f227,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f77,f197,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f197,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f36,f37,f34,f69,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f69,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f77,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f34,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f270,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f269,plain,
    ( v3_waybel_7(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v3_waybel_7(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f268,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f267,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f271,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f266,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f35,f36,f34,f231,f261,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_xboole_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f261,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f76,f231,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f76,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f37,f34,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f232,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f227,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f196,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f59,f82,f183,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f183,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f181,f154])).

fof(f154,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f34,f68,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f181,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f35,f37,f36,f73,f93,f103,f98,f34,f122,f117,f108,f129,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X1,X3)
      | ~ r2_waybel_7(X0,X3,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f108,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_7
  <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f117,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_8
  <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f122,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_9
  <=> v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f98,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f103,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_6
  <=> r2_waybel_7(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f93,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_2
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f82,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f152,plain,
    ( spl6_1
    | spl6_11 ),
    inference(avatar_split_clause,[],[f24,f150,f67])).

fof(f24,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ r2_hidden(sK1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_waybel_7(sK0,X2,X3)
      | r2_hidden(X3,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f130,plain,
    ( ~ spl6_1
    | spl6_10 ),
    inference(avatar_split_clause,[],[f32,f127,f67])).

fof(f32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f123,plain,
    ( ~ spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f31,f120,f67])).

fof(f31,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f118,plain,
    ( ~ spl6_1
    | spl6_8 ),
    inference(avatar_split_clause,[],[f30,f115,f67])).

fof(f30,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,
    ( ~ spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f29,f106,f67])).

fof(f29,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f104,plain,
    ( ~ spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f26,f101,f67])).

fof(f26,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f99,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f25,f96,f67])).

fof(f25,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f33,f91,f67])).

fof(f33,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f27,f80,f67])).

fof(f27,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f28,f71,f67])).

fof(f28,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
