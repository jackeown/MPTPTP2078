%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1114+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:17 EST 2020

% Result     : Theorem 3.79s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  147 (1255 expanded)
%              Number of leaves         :   28 ( 445 expanded)
%              Depth                    :   20
%              Number of atoms          :  761 (13565 expanded)
%              Number of equality atoms :   47 ( 189 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f119,f124,f128,f4666,f5212])).

fof(f5212,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f5210])).

fof(f5210,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f4684,f5207,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f5207,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f5206,f4727])).

fof(f4727,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f5206,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f55,f4725,f5198,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f5198,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f54,f56,f55,f103,f4731,f134,f4734,f4725,f97])).

fof(f97,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ( ( ( r1_xboole_0(X1,sK5(X0,X1,X2))
                        & r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
                        & v3_pre_topc(sK5(X0,X1,X2),X0)
                        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( ~ r1_xboole_0(X1,X5)
                          | ~ r2_hidden(sK4(X0,X1,X2),X5)
                          | ~ v3_pre_topc(X5,X0)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                      | r2_hidden(sK4(X0,X1,X2),X2) )
                    & r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( r1_xboole_0(X1,sK6(X0,X1,X6))
                            & r2_hidden(X6,sK6(X0,X1,X6))
                            & v3_pre_topc(sK6(X0,X1,X6),X0)
                            & m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X1,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X1,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X0)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X1,X4)
              & r2_hidden(sK4(X0,X1,X2),X4)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X1,X5)
              | ~ r2_hidden(sK4(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X1,X4)
          & r2_hidden(sK4(X0,X1,X2),X4)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK5(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X1,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK6(X0,X1,X6))
        & r2_hidden(X6,sK6(X0,X1,X6))
        & v3_pre_topc(sK6(X0,X1,X6),X0)
        & m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( ~ r1_xboole_0(X1,X5)
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( r1_xboole_0(X1,X7)
                              & r2_hidden(X6,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f4734,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f4733,f4726])).

fof(f4726,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK3) = k3_subset_1(u1_struct_0(sK0),sK3)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f123,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f4733,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f4732,f166])).

fof(f166,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0) = k4_xboole_0(u1_struct_0(sK0),X0) ),
    inference(unit_resulting_resolution,[],[f133,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f133,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f131,f132])).

fof(f132,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f129,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f54,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f131,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f129,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f4732,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3),sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f4723,f132])).

fof(f4723,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3),sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f54,f118,f123,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f118,plain,
    ( v4_pre_topc(sK3,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_4
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f134,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f54,f55,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f4731,plain,
    ( r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),sK3))
    | spl8_2
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f4668,f4726])).

fof(f4668,plain,
    ( r2_hidden(sK2,k4_xboole_0(u1_struct_0(sK0),sK3))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f56,f108,f98])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f108,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f103,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_1
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f56,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ( ~ r2_hidden(sK2,sK3)
        & r1_tarski(sK1,sK3)
        & v4_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( r2_hidden(sK2,X4)
          | ~ r1_tarski(sK1,X4)
          | ~ v4_pre_topc(X4,sK0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & r2_hidden(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & r2_hidden(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X2,X3)
                    & r1_tarski(X1,X3)
                    & v4_pre_topc(X3,sK0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( r2_hidden(X2,X4)
                    | ~ r1_tarski(X1,X4)
                    | ~ v4_pre_topc(X4,sK0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & r2_hidden(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v4_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ! [X4] :
                  ( r2_hidden(X2,X4)
                  | ~ r1_tarski(X1,X4)
                  | ~ v4_pre_topc(X4,sK0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & r2_hidden(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r1_tarski(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r1_tarski(sK1,X4)
                | ~ v4_pre_topc(X4,sK0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & r2_hidden(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X2,X3)
              & r1_tarski(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ! [X4] :
              ( r2_hidden(X2,X4)
              | ~ r1_tarski(sK1,X4)
              | ~ v4_pre_topc(X4,sK0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & r2_hidden(X2,u1_struct_0(sK0)) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK2,X3)
            & r1_tarski(sK1,X3)
            & v4_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ! [X4] :
            ( r2_hidden(sK2,X4)
            | ~ r1_tarski(sK1,X4)
            | ~ v4_pre_topc(X4,sK0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & r2_hidden(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK2,X3)
        & r1_tarski(sK1,X3)
        & v4_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(sK1,sK3)
      & v4_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X2,X3)
                    & r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( r2_hidden(X2,X4)
                    | ~ r1_tarski(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & r2_hidden(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X2,X3)
                    & r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & r2_hidden(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X2,X3)
                    & r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & r2_hidden(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & r2_hidden(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & r2_hidden(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( r2_hidden(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( r1_tarski(X1,X3)
                          & v4_pre_topc(X3,X0) )
                       => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f4725,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f123,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f4684,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK3))
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f113,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f113,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f4666,plain,
    ( spl8_1
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f4664])).

fof(f4664,plain,
    ( $false
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f54,f56,f55,f104,f134,f4656,f95])).

fof(f95,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK6(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK6(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4656,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f4655,f737])).

fof(f737,plain,
    ( sK6(sK0,sK1,sK2) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f733,f255])).

fof(f255,plain,
    ( sK6(sK0,sK1,sK2) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f170,f80])).

fof(f170,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f54,f56,f104,f55,f134,f96])).

fof(f96,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f733,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f253,f79])).

fof(f253,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f170,f78])).

fof(f4655,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f4654,f166])).

fof(f4654,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f4653,f132])).

fof(f4653,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f54,f253,f4598,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4598,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f256,f253,f4550,f127])).

fof(f127,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,X4)
        | ~ v4_pre_topc(X4,sK0)
        | ~ r1_tarski(sK1,X4) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_6
  <=> ! [X4] :
        ( r2_hidden(sK2,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X4,sK0)
        | ~ r1_tarski(sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f4550,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))
    | spl8_1 ),
    inference(superposition,[],[f187,f254])).

fof(f254,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),sK6(sK0,sK1,sK2))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f170,f79])).

fof(f187,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k4_xboole_0(X0,sK6(sK0,sK1,sK2)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f172,f99])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f172,plain,
    ( r2_hidden(sK2,sK6(sK0,sK1,sK2))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f54,f56,f104,f55,f134,f94])).

fof(f94,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | r2_hidden(X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f256,plain,
    ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f55,f173,f170,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f173,plain,
    ( r1_xboole_0(sK1,sK6(sK0,sK1,sK2))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f54,f56,f104,f55,f134,f93])).

fof(f93,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X1,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f128,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f57,f126,f102])).

fof(f57,plain,(
    ! [X4] :
      ( r2_hidden(sK2,X4)
      | ~ r1_tarski(sK1,X4)
      | ~ v4_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f58,f121,f102])).

fof(f58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f59,f116,f102])).

fof(f59,plain,
    ( v4_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f60,f111,f102])).

fof(f60,plain,
    ( r1_tarski(sK1,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f61,f106,f102])).

fof(f61,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
