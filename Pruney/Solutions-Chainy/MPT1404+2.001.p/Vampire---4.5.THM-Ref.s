%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 923 expanded)
%              Number of leaves         :   17 ( 337 expanded)
%              Depth                    :   15
%              Number of atoms          :  529 (8871 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f79,f92,f110])).

fof(f110,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f108,f105])).

fof(f105,plain,
    ( ~ r1_xboole_0(sK1,sK5(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f41,f43,f42,f64,f103,f101,f100,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK4(X0,X1,X2))
                    & r2_hidden(X2,sK4(X0,X1,X2))
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK4(X0,X1,X2))
        & r2_hidden(X2,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f100,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK5(X0,X1,X2))
                    & r1_tarski(sK5(X0,X1,X2),X2)
                    & v3_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK5(X0,X1,X2))
        & r1_tarski(sK5(X0,X1,X2),X2)
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f74,plain,
    ( m1_connsp_2(sK3,sK0,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_3
  <=> m1_connsp_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( r1_xboole_0(sK3,sK1)
        & m1_connsp_2(sK3,sK0,sK2) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(X4,sK1)
          | ~ m1_connsp_2(X4,sK0,sK2) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,sK0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,sK0,X2) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X3,X1)
                  & m1_connsp_2(X3,sK0,X2) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X4,X1)
                  | ~ m1_connsp_2(X4,sK0,X2) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X3,sK1)
                & m1_connsp_2(X3,sK0,X2) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X4,sK1)
                | ~ m1_connsp_2(X4,sK0,X2) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( r1_xboole_0(X3,sK1)
              & m1_connsp_2(X3,sK0,X2) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X4,sK1)
              | ~ m1_connsp_2(X4,sK0,X2) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ? [X3] :
            ( r1_xboole_0(X3,sK1)
            & m1_connsp_2(X3,sK0,sK2) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X4,sK1)
            | ~ m1_connsp_2(X4,sK0,sK2) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( r1_xboole_0(X3,sK1)
        & m1_connsp_2(X3,sK0,sK2) )
   => ( r1_xboole_0(sK3,sK1)
      & m1_connsp_2(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_connsp_2(X3,X0,X2)
                     => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,
    ( v3_pre_topc(sK5(sK0,sK2,sK3),sK0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,
    ( r2_hidden(sK2,sK5(sK0,sK2,sK3))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK5(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_1
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( r1_xboole_0(sK1,sK5(sK0,sK2,sK3))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f104,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f104,plain,
    ( r1_xboole_0(sK5(sK0,sK2,sK3),sK1)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f69,f102,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f102,plain,
    ( r1_tarski(sK5(sK0,sK2,sK3),sK3)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK5(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f92,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f89,f88])).

fof(f88,plain,
    ( m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f81,f80,f83,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f83,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,
    ( r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK2)
    | spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f86,f78])).

fof(f78,plain,
    ( ! [X4] :
        ( ~ m1_connsp_2(X4,sK0,sK2)
        | ~ r1_xboole_0(X4,sK1) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_4
  <=> ! [X4] :
        ( ~ r1_xboole_0(X4,sK1)
        | ~ m1_connsp_2(X4,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f86,plain,
    ( r1_xboole_0(sK4(sK0,sK1,sK2),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f82,f59])).

fof(f82,plain,
    ( r1_xboole_0(sK1,sK4(sK0,sK1,sK2))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,sK4(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f44,f77,f63])).

fof(f44,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,sK1)
      | ~ m1_connsp_2(X4,sK0,sK2)
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f45,f72,f63])).

fof(f45,plain,
    ( m1_connsp_2(sK3,sK0,sK2)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f67,f63])).

fof(f46,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (16415)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (16402)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.47  % (16403)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.47  % (16407)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % (16415)Refutation not found, incomplete strategy% (16415)------------------------------
% 0.22/0.47  % (16415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (16415)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (16415)Memory used [KB]: 895
% 0.22/0.47  % (16415)Time elapsed: 0.063 s
% 0.22/0.47  % (16415)------------------------------
% 0.22/0.47  % (16415)------------------------------
% 0.22/0.48  % (16403)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (16419)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f70,f75,f79,f92,f110])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    $false | (~spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f105])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK5(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_3)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f41,f43,f42,f64,f103,f101,f100,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK4(X0,X1,X2)) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK4(X0,X1,X2)) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(rectify,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    m1_subset_1(sK5(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X2) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X2) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(rectify,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    m1_connsp_2(sK3,sK0,sK2) | ~spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl6_3 <=> m1_connsp_2(sK3,sK0,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ((((r1_xboole_0(sK3,sK1) & m1_connsp_2(sK3,sK0,sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(X4,sK1) | ~m1_connsp_2(X4,sK0,sK2)) | r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,sK0,X2)) | ~r2_hidden(X2,k2_pre_topc(sK0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,sK0,X2)) | r2_hidden(X2,k2_pre_topc(sK0,X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,sK0,X2)) | ~r2_hidden(X2,k2_pre_topc(sK0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,sK0,X2)) | r2_hidden(X2,k2_pre_topc(sK0,X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : ((? [X3] : (r1_xboole_0(X3,sK1) & m1_connsp_2(X3,sK0,X2)) | ~r2_hidden(X2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(X4,sK1) | ~m1_connsp_2(X4,sK0,X2)) | r2_hidden(X2,k2_pre_topc(sK0,sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ? [X2] : ((? [X3] : (r1_xboole_0(X3,sK1) & m1_connsp_2(X3,sK0,X2)) | ~r2_hidden(X2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(X4,sK1) | ~m1_connsp_2(X4,sK0,X2)) | r2_hidden(X2,k2_pre_topc(sK0,sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((? [X3] : (r1_xboole_0(X3,sK1) & m1_connsp_2(X3,sK0,sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(X4,sK1) | ~m1_connsp_2(X4,sK0,sK2)) | r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ? [X3] : (r1_xboole_0(X3,sK1) & m1_connsp_2(X3,sK0,sK2)) => (r1_xboole_0(sK3,sK1) & m1_connsp_2(sK3,sK0,sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(rectify,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => ~r1_xboole_0(X3,X1))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => ~r1_xboole_0(X3,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    v3_pre_topc(sK5(sK0,sK2,sK3),sK0) | ~spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(sK5(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    r2_hidden(sK2,sK5(sK0,sK2,sK3)) | ~spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,sK5(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | ~spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl6_1 <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    r1_xboole_0(sK1,sK5(sK0,sK2,sK3)) | (~spl6_2 | ~spl6_3)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f104,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    r1_xboole_0(sK5(sK0,sK2,sK3),sK1) | (~spl6_2 | ~spl6_3)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f69,f102,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    r1_tarski(sK5(sK0,sK2,sK3),sK3) | ~spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f74,f97,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(sK5(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    r1_xboole_0(sK3,sK1) | ~spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl6_2 <=> r1_xboole_0(sK3,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl6_1 | ~spl6_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    $false | (spl6_1 | ~spl6_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f89,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK2) | spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f43,f81,f80,f83,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X1,X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    r2_hidden(sK2,sK4(sK0,sK1,sK2)) | spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,sK4(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ~m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK2) | (spl6_1 | ~spl6_4)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f86,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X4] : (~m1_connsp_2(X4,sK0,sK2) | ~r1_xboole_0(X4,sK1)) ) | ~spl6_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl6_4 <=> ! [X4] : (~r1_xboole_0(X4,sK1) | ~m1_connsp_2(X4,sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    r1_xboole_0(sK4(sK0,sK1,sK2),sK1) | spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f82,f59])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    r1_xboole_0(sK1,sK4(sK0,sK1,sK2)) | spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f41,f39,f43,f65,f42,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X1,sK4(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl6_1 | spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f44,f77,f63])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X4] : (~r1_xboole_0(X4,sK1) | ~m1_connsp_2(X4,sK0,sK2) | r2_hidden(sK2,k2_pre_topc(sK0,sK1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ~spl6_1 | spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f72,f63])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    m1_connsp_2(sK3,sK0,sK2) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ~spl6_1 | spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f46,f67,f63])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    r1_xboole_0(sK3,sK1) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (16403)------------------------------
% 0.22/0.48  % (16403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16403)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (16403)Memory used [KB]: 9978
% 0.22/0.48  % (16403)Time elapsed: 0.067 s
% 0.22/0.48  % (16403)------------------------------
% 0.22/0.48  % (16403)------------------------------
% 0.22/0.49  % (16399)Success in time 0.124 s
%------------------------------------------------------------------------------
