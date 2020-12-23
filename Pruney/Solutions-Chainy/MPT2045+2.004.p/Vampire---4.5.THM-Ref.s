%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  161 (2267 expanded)
%              Number of leaves         :   22 ( 713 expanded)
%              Depth                    :   21
%              Number of atoms          :  813 (17640 expanded)
%              Number of equality atoms :    6 ( 156 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f108,f203,f228])).

fof(f228,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f226,f221])).

fof(f221,plain,
    ( r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2)
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f101,f215,f213,f212,f182])).

fof(f182,plain,(
    ! [X37,X35,X36] :
      ( ~ v3_pre_topc(X35,sK0)
      | r2_hidden(X35,X36)
      | ~ r2_hidden(X37,X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_waybel_7(sK0,X36,X37) ) ),
    inference(subsumption_resolution,[],[f181,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
      | ~ r2_waybel_7(sK0,sK2,sK1) )
    & ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
      | r2_waybel_7(sK0,sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | r2_waybel_7(X0,X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(sK0,X1),X2)
                | ~ r2_waybel_7(sK0,X2,X1) )
              & ( r1_tarski(k1_yellow19(sK0,X1),X2)
                | r2_waybel_7(sK0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k1_yellow19(sK0,X1),X2)
              | ~ r2_waybel_7(sK0,X2,X1) )
            & ( r1_tarski(k1_yellow19(sK0,X1),X2)
              | r2_waybel_7(sK0,X2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),X2)
            | ~ r2_waybel_7(sK0,X2,sK1) )
          & ( r1_tarski(k1_yellow19(sK0,sK1),X2)
            | r2_waybel_7(sK0,X2,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),X2)
          | ~ r2_waybel_7(sK0,X2,sK1) )
        & ( r1_tarski(k1_yellow19(sK0,sK1),X2)
          | r2_waybel_7(sK0,X2,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
   => ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
        | ~ r2_waybel_7(sK0,sK2,sK1) )
      & ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
        | r2_waybel_7(sK0,sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
               => ( r2_waybel_7(X0,X2,X1)
                <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

fof(f181,plain,(
    ! [X37,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X35,X36)
      | ~ r2_hidden(X37,X35)
      | ~ v3_pre_topc(X35,sK0)
      | ~ r2_waybel_7(sK0,X36,X37)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f153,plain,(
    ! [X37,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X35,X36)
      | ~ r2_hidden(X37,X35)
      | ~ v3_pre_topc(X35,sK0)
      | ~ r2_waybel_7(sK0,X36,X37)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f74,f128])).

fof(f128,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f109,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f109,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f57,f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(X2,sK4(X0,X1,X2))
              & v3_pre_topc(sK4(X0,X1,X2),X0)
              & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(X2,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f212,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f208,f210,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f158,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f56])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f57])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f66,f128])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK3(X0,X1,X2))
                    & r1_tarski(sK3(X0,X1,X2),X2)
                    & v3_pre_topc(sK3(X0,X1,X2),X0)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X2)
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f210,plain,
    ( m1_subset_1(sK7(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f208,f187])).

fof(f187,plain,(
    ! [X41,X40] :
      ( m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X40,sK0,X41)
      | ~ m1_subset_1(X41,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f186,f55])).

fof(f186,plain,(
    ! [X41,X40] :
      ( m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X40,sK0,X41)
      | ~ m1_subset_1(X41,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f56])).

fof(f185,plain,(
    ! [X41,X40] :
      ( m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X40,sK0,X41)
      | ~ m1_subset_1(X41,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f57])).

fof(f155,plain,(
    ! [X41,X40] :
      ( m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X40,sK0,X41)
      | ~ m1_subset_1(X41,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f84,f128])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f208,plain,
    ( m1_connsp_2(sK7(k1_yellow19(sK0,sK1),sK2),sK0,sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f205,f174])).

fof(f174,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | m1_connsp_2(X28,sK0,X27)
      | ~ r2_hidden(X28,k1_yellow19(sK0,X27)) ) ),
    inference(subsumption_resolution,[],[f173,f55])).

fof(f173,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | m1_connsp_2(X28,sK0,X27)
      | ~ r2_hidden(X28,k1_yellow19(sK0,X27))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f56])).

fof(f172,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | m1_connsp_2(X28,sK0,X27)
      | ~ r2_hidden(X28,k1_yellow19(sK0,X27))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f57])).

fof(f149,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | m1_connsp_2(X28,sK0,X27)
      | ~ r2_hidden(X28,k1_yellow19(sK0,X27))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f71,f128])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k1_yellow19(X0,X1))
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

fof(f205,plain,
    ( r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f106,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f106,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_2
  <=> r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f111,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f110,f109])).

fof(f110,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f58,f64])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f213,plain,
    ( v3_pre_topc(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK0)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f208,f210,f162])).

fof(f162,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK0))
      | v3_pre_topc(sK3(sK0,X6,X7),sK0)
      | ~ m1_connsp_2(X7,sK0,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f161,f55])).

fof(f161,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK0))
      | v3_pre_topc(sK3(sK0,X6,X7),sK0)
      | ~ m1_connsp_2(X7,sK0,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f160,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK0))
      | v3_pre_topc(sK3(sK0,X6,X7),sK0)
      | ~ m1_connsp_2(X7,sK0,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f57])).

fof(f140,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK0))
      | v3_pre_topc(sK3(sK0,X6,X7),sK0)
      | ~ m1_connsp_2(X7,sK0,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f67,f128])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f215,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f208,f210,f168])).

fof(f168,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,k2_struct_0(sK0))
      | r2_hidden(X14,sK3(sK0,X14,X15))
      | ~ m1_connsp_2(X15,sK0,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f167,f55])).

fof(f167,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,k2_struct_0(sK0))
      | r2_hidden(X14,sK3(sK0,X14,X15))
      | ~ m1_connsp_2(X15,sK0,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f166,f56])).

fof(f166,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,k2_struct_0(sK0))
      | r2_hidden(X14,sK3(sK0,X14,X15))
      | ~ m1_connsp_2(X15,sK0,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f57])).

fof(f144,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,k2_struct_0(sK0))
      | r2_hidden(X14,sK3(sK0,X14,X15))
      | ~ m1_connsp_2(X15,sK0,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f69,f128])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,
    ( r2_waybel_7(sK0,sK2,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_1
  <=> r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f226,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f214,f219,f97])).

fof(f97,plain,(
    ! [X4,X5,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X4,X5)
      | sP8(X5,X1) ) ),
    inference(cnf_transformation,[],[f97_D])).

fof(f97_D,plain,(
    ! [X1,X5] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
          | ~ r1_tarski(X4,X5) )
    <=> ~ sP8(X5,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

% (925)Refutation not found, incomplete strategy% (925)------------------------------
% (925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (953)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (925)Termination reason: Refutation not found, incomplete strategy

% (925)Memory used [KB]: 10874
% (925)Time elapsed: 0.158 s
% (925)------------------------------
% (925)------------------------------
fof(f219,plain,
    ( ~ sP8(sK7(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f91,f206,f90,f216,f98])).

fof(f98,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_tarski(X5,X0)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ sP8(X5,X1) ) ),
    inference(general_splitting,[],[f96,f97_D])).

fof(f96,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f79,f63,f63])).

fof(f63,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f79,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK6(X0,X1),X1)
            & r2_hidden(sK5(X0,X1),X1)
            & r1_tarski(sK6(X0,X1),X0)
            & r1_tarski(sK5(X0,X1),sK6(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r1_tarski(sK6(X0,X1),X0)
        & r1_tarski(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X2,X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ r1_tarski(X3,X0)
              | ~ r1_tarski(X2,X3) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f216,plain,
    ( r1_tarski(sK7(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f210,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f36])).

fof(f206,plain,
    ( ~ r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f106,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f214,plain,
    ( r1_tarski(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK7(k1_yellow19(sK0,sK1),sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f208,f210,f165])).

fof(f165,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r1_tarski(sK3(sK0,X10,X11),X11)
      | ~ m1_connsp_2(X11,sK0,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f164,f55])).

fof(f164,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r1_tarski(sK3(sK0,X10,X11),X11)
      | ~ m1_connsp_2(X11,sK0,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f56])).

fof(f163,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r1_tarski(sK3(sK0,X10,X11),X11)
      | ~ m1_connsp_2(X11,sK0,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f57])).

fof(f142,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r1_tarski(sK3(sK0,X10,X11),X11)
      | ~ m1_connsp_2(X11,sK0,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f68,f128])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f203,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f201,f192])).

fof(f192,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f132,f111,f177])).

fof(f177,plain,(
    ! [X30,X29] :
      ( ~ m1_subset_1(X29,k2_struct_0(sK0))
      | r2_hidden(X30,k1_yellow19(sK0,X29))
      | ~ m1_connsp_2(X30,sK0,X29) ) ),
    inference(subsumption_resolution,[],[f176,f55])).

fof(f176,plain,(
    ! [X30,X29] :
      ( ~ m1_subset_1(X29,k2_struct_0(sK0))
      | r2_hidden(X30,k1_yellow19(sK0,X29))
      | ~ m1_connsp_2(X30,sK0,X29)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f56])).

fof(f175,plain,(
    ! [X30,X29] :
      ( ~ m1_subset_1(X29,k2_struct_0(sK0))
      | r2_hidden(X30,k1_yellow19(sK0,X29))
      | ~ m1_connsp_2(X30,sK0,X29)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f57])).

fof(f150,plain,(
    ! [X30,X29] :
      ( ~ m1_subset_1(X29,k2_struct_0(sK0))
      | r2_hidden(X30,k1_yellow19(sK0,X29))
      | ~ m1_connsp_2(X30,sK0,X29)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f72,f128])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),k1_yellow19(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f105,f115,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f56,f57,f102,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f105,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f201,plain,
    ( m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f111,f114,f113,f129,f180])).

fof(f180,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k2_struct_0(sK0))
      | m1_connsp_2(X31,sK0,X32)
      | ~ r2_hidden(X32,X31)
      | ~ v3_pre_topc(X31,sK0)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f179,f55])).

fof(f179,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X31,sK0,X32)
      | ~ r2_hidden(X32,X31)
      | ~ v3_pre_topc(X31,sK0)
      | ~ m1_subset_1(X32,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f56])).

fof(f178,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X31,sK0,X32)
      | ~ r2_hidden(X32,X31)
      | ~ v3_pre_topc(X31,sK0)
      | ~ m1_subset_1(X32,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f57])).

fof(f151,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X31,sK0,X32)
      | ~ r2_hidden(X32,X31)
      | ~ v3_pre_topc(X31,sK0)
      | ~ m1_subset_1(X32,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f73,f128])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f129,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1 ),
    inference(backward_demodulation,[],[f112,f128])).

fof(f112,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f56,f57,f102,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK1),sK0)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f56,f57,f102,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f114,plain,
    ( r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f56,f57,f102,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK4(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f108,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f61,f104,f100])).

fof(f61,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f62,f104,f100])).

fof(f62,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (928)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (934)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (923)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (944)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (937)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (924)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (929)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (930)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (954)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (927)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (925)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (926)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (955)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (931)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (932)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (949)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (941)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (946)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (950)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (933)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (951)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (936)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (947)Refutation not found, incomplete strategy% (947)------------------------------
% 0.20/0.55  % (947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (947)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (947)Memory used [KB]: 10746
% 0.20/0.55  % (947)Time elapsed: 0.097 s
% 0.20/0.55  % (947)------------------------------
% 0.20/0.55  % (947)------------------------------
% 0.20/0.56  % (952)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (939)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (935)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (940)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (938)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (952)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f229,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f107,f108,f203,f228])).
% 0.20/0.56  fof(f228,plain,(
% 0.20/0.56    ~spl9_1 | spl9_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 0.20/0.56  fof(f227,plain,(
% 0.20/0.56    $false | (~spl9_1 | spl9_2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f226,f221])).
% 0.20/0.56  fof(f221,plain,(
% 0.20/0.56    r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2) | (~spl9_1 | spl9_2)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f101,f215,f213,f212,f182])).
% 0.20/0.56  fof(f182,plain,(
% 0.20/0.56    ( ! [X37,X35,X36] : (~v3_pre_topc(X35,sK0) | r2_hidden(X35,X36) | ~r2_hidden(X37,X35) | ~m1_subset_1(X35,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_waybel_7(sK0,X36,X37)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f181,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    v2_pre_topc(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    (((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) => ((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.20/0.56    inference(negated_conjecture,[],[f12])).
% 0.20/0.56  fof(f12,conjecture,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).
% 0.20/0.56  fof(f181,plain,(
% 0.20/0.56    ( ! [X37,X35,X36] : (~m1_subset_1(X35,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X35,X36) | ~r2_hidden(X37,X35) | ~v3_pre_topc(X35,sK0) | ~r2_waybel_7(sK0,X36,X37) | ~v2_pre_topc(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f153,f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    l1_pre_topc(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    ( ! [X37,X35,X36] : (~m1_subset_1(X35,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X35,X36) | ~r2_hidden(X37,X35) | ~v3_pre_topc(X35,sK0) | ~r2_waybel_7(sK0,X36,X37) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f74,f128])).
% 0.20/0.56  fof(f128,plain,(
% 0.20/0.56    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f109,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    l1_struct_0(sK0)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f57,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(rectify,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).
% 0.20/0.56  fof(f212,plain,(
% 0.20/0.56    m1_subset_1(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f111,f208,f210,f159])).
% 0.20/0.56  fof(f159,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f158,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ~v2_struct_0(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f157,f56])).
% 0.20/0.56  fof(f157,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f137,f57])).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f66,f128])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(rectify,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.20/0.56  fof(f210,plain,(
% 0.20/0.56    m1_subset_1(sK7(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f111,f208,f187])).
% 0.20/0.56  fof(f187,plain,(
% 0.20/0.56    ( ! [X41,X40] : (m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X40,sK0,X41) | ~m1_subset_1(X41,k2_struct_0(sK0))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f186,f55])).
% 0.20/0.56  fof(f186,plain,(
% 0.20/0.56    ( ! [X41,X40] : (m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X40,sK0,X41) | ~m1_subset_1(X41,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f185,f56])).
% 0.20/0.56  fof(f185,plain,(
% 0.20/0.56    ( ! [X41,X40] : (m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X40,sK0,X41) | ~m1_subset_1(X41,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f155,f57])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ( ! [X41,X40] : (m1_subset_1(X40,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X40,sK0,X41) | ~m1_subset_1(X41,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f84,f128])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.56  fof(f208,plain,(
% 0.20/0.56    m1_connsp_2(sK7(k1_yellow19(sK0,sK1),sK2),sK0,sK1) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f111,f205,f174])).
% 0.20/0.56  fof(f174,plain,(
% 0.20/0.56    ( ! [X28,X27] : (~m1_subset_1(X27,k2_struct_0(sK0)) | m1_connsp_2(X28,sK0,X27) | ~r2_hidden(X28,k1_yellow19(sK0,X27))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f173,f55])).
% 0.20/0.56  fof(f173,plain,(
% 0.20/0.56    ( ! [X28,X27] : (~m1_subset_1(X27,k2_struct_0(sK0)) | m1_connsp_2(X28,sK0,X27) | ~r2_hidden(X28,k1_yellow19(sK0,X27)) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f172,f56])).
% 0.20/0.56  fof(f172,plain,(
% 0.20/0.56    ( ! [X28,X27] : (~m1_subset_1(X27,k2_struct_0(sK0)) | m1_connsp_2(X28,sK0,X27) | ~r2_hidden(X28,k1_yellow19(sK0,X27)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f149,f57])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    ( ! [X28,X27] : (~m1_subset_1(X27,k2_struct_0(sK0)) | m1_connsp_2(X28,sK0,X27) | ~r2_hidden(X28,k1_yellow19(sK0,X27)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f71,f128])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).
% 0.20/0.56  fof(f205,plain,(
% 0.20/0.56    r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1)) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f106,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | spl9_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f104])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    spl9_2 <=> r1_tarski(k1_yellow19(sK0,sK1),sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.56    inference(subsumption_resolution,[],[f110,f109])).
% 0.20/0.56  fof(f110,plain,(
% 0.20/0.56    m1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.56    inference(superposition,[],[f58,f64])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f213,plain,(
% 0.20/0.56    v3_pre_topc(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK0) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f111,f208,f210,f162])).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    ( ! [X6,X7] : (~m1_subset_1(X6,k2_struct_0(sK0)) | v3_pre_topc(sK3(sK0,X6,X7),sK0) | ~m1_connsp_2(X7,sK0,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f161,f55])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    ( ! [X6,X7] : (~m1_subset_1(X6,k2_struct_0(sK0)) | v3_pre_topc(sK3(sK0,X6,X7),sK0) | ~m1_connsp_2(X7,sK0,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f160,f56])).
% 0.20/0.56  fof(f160,plain,(
% 0.20/0.56    ( ! [X6,X7] : (~m1_subset_1(X6,k2_struct_0(sK0)) | v3_pre_topc(sK3(sK0,X6,X7),sK0) | ~m1_connsp_2(X7,sK0,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f140,f57])).
% 0.20/0.56  fof(f140,plain,(
% 0.20/0.56    ( ! [X6,X7] : (~m1_subset_1(X6,k2_struct_0(sK0)) | v3_pre_topc(sK3(sK0,X6,X7),sK0) | ~m1_connsp_2(X7,sK0,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f67,f128])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (v3_pre_topc(sK3(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f215,plain,(
% 0.20/0.56    r2_hidden(sK1,sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2))) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f111,f208,f210,f168])).
% 0.20/0.56  fof(f168,plain,(
% 0.20/0.56    ( ! [X14,X15] : (~m1_subset_1(X14,k2_struct_0(sK0)) | r2_hidden(X14,sK3(sK0,X14,X15)) | ~m1_connsp_2(X15,sK0,X14) | ~m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f167,f55])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ( ! [X14,X15] : (~m1_subset_1(X14,k2_struct_0(sK0)) | r2_hidden(X14,sK3(sK0,X14,X15)) | ~m1_connsp_2(X15,sK0,X14) | ~m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f166,f56])).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    ( ! [X14,X15] : (~m1_subset_1(X14,k2_struct_0(sK0)) | r2_hidden(X14,sK3(sK0,X14,X15)) | ~m1_connsp_2(X15,sK0,X14) | ~m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f144,f57])).
% 0.20/0.56  fof(f144,plain,(
% 0.20/0.56    ( ! [X14,X15] : (~m1_subset_1(X14,k2_struct_0(sK0)) | r2_hidden(X14,sK3(sK0,X14,X15)) | ~m1_connsp_2(X15,sK0,X14) | ~m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f69,f128])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,sK3(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    r2_waybel_7(sK0,sK2,sK1) | ~spl9_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f100])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    spl9_1 <=> r2_waybel_7(sK0,sK2,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.56  fof(f226,plain,(
% 0.20/0.56    ~r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2) | spl9_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f214,f219,f97])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    ( ! [X4,X5,X1] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5) | sP8(X5,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f97_D])).
% 0.20/0.56  fof(f97_D,plain,(
% 0.20/0.56    ( ! [X1,X5] : (( ! [X4] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5)) ) <=> ~sP8(X5,X1)) )),
% 0.20/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.56  % (925)Refutation not found, incomplete strategy% (925)------------------------------
% 0.20/0.56  % (925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (953)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (925)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (925)Memory used [KB]: 10874
% 0.20/0.57  % (925)Time elapsed: 0.158 s
% 0.20/0.57  % (925)------------------------------
% 0.20/0.57  % (925)------------------------------
% 0.20/0.58  fof(f219,plain,(
% 0.20/0.58    ~sP8(sK7(k1_yellow19(sK0,sK1),sK2),sK2) | spl9_2),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f91,f206,f90,f216,f98])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X0) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~sP8(X5,X1)) )),
% 0.20/0.58    inference(general_splitting,[],[f96,f97_D])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f79,f63,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.20/0.58  fof(f79,plain,(
% 0.20/0.58    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r1_tarski(sK6(X0,X1),X0) & r1_tarski(sK5(X0,X1),sK6(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f47,f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r1_tarski(sK6(X0,X1),X0) & r1_tarski(sK5(X0,X1),sK6(X0,X1))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.58    inference(rectify,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.58    inference(nnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.58    inference(flattening,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).
% 0.20/0.58  fof(f216,plain,(
% 0.20/0.58    r1_tarski(sK7(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0)) | spl9_2),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f210,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.58    inference(nnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.20/0.58    inference(definition_unfolding,[],[f60,f63])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f206,plain,(
% 0.20/0.58    ~r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),sK2) | spl9_2),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f106,f87])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.20/0.58    inference(definition_unfolding,[],[f59,f63])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f214,plain,(
% 0.20/0.58    r1_tarski(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK7(k1_yellow19(sK0,sK1),sK2)) | spl9_2),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f111,f208,f210,f165])).
% 0.20/0.58  fof(f165,plain,(
% 0.20/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r1_tarski(sK3(sK0,X10,X11),X11) | ~m1_connsp_2(X11,sK0,X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f164,f55])).
% 0.20/0.58  fof(f164,plain,(
% 0.20/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r1_tarski(sK3(sK0,X10,X11),X11) | ~m1_connsp_2(X11,sK0,X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f163,f56])).
% 0.20/0.58  fof(f163,plain,(
% 0.20/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r1_tarski(sK3(sK0,X10,X11),X11) | ~m1_connsp_2(X11,sK0,X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f142,f57])).
% 0.20/0.58  fof(f142,plain,(
% 0.20/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r1_tarski(sK3(sK0,X10,X11),X11) | ~m1_connsp_2(X11,sK0,X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(superposition,[],[f68,f128])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f40])).
% 0.20/0.58  fof(f203,plain,(
% 0.20/0.58    spl9_1 | ~spl9_2),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.58  fof(f202,plain,(
% 0.20/0.58    $false | (spl9_1 | ~spl9_2)),
% 0.20/0.58    inference(subsumption_resolution,[],[f201,f192])).
% 0.20/0.58  fof(f192,plain,(
% 0.20/0.58    ~m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1) | (spl9_1 | ~spl9_2)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f132,f111,f177])).
% 0.20/0.58  fof(f177,plain,(
% 0.20/0.58    ( ! [X30,X29] : (~m1_subset_1(X29,k2_struct_0(sK0)) | r2_hidden(X30,k1_yellow19(sK0,X29)) | ~m1_connsp_2(X30,sK0,X29)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f176,f55])).
% 0.20/0.58  fof(f176,plain,(
% 0.20/0.58    ( ! [X30,X29] : (~m1_subset_1(X29,k2_struct_0(sK0)) | r2_hidden(X30,k1_yellow19(sK0,X29)) | ~m1_connsp_2(X30,sK0,X29) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f175,f56])).
% 0.20/0.58  fof(f175,plain,(
% 0.20/0.58    ( ! [X30,X29] : (~m1_subset_1(X29,k2_struct_0(sK0)) | r2_hidden(X30,k1_yellow19(sK0,X29)) | ~m1_connsp_2(X30,sK0,X29) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f150,f57])).
% 0.20/0.58  fof(f150,plain,(
% 0.20/0.58    ( ! [X30,X29] : (~m1_subset_1(X29,k2_struct_0(sK0)) | r2_hidden(X30,k1_yellow19(sK0,X29)) | ~m1_connsp_2(X30,sK0,X29) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(superposition,[],[f72,f128])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f132,plain,(
% 0.20/0.58    ~r2_hidden(sK4(sK0,sK2,sK1),k1_yellow19(sK0,sK1)) | (spl9_1 | ~spl9_2)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f105,f115,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    ~r2_hidden(sK4(sK0,sK2,sK1),sK2) | spl9_1),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f56,f57,f102,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f45])).
% 0.20/0.58  fof(f102,plain,(
% 0.20/0.58    ~r2_waybel_7(sK0,sK2,sK1) | spl9_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f100])).
% 0.20/0.58  fof(f105,plain,(
% 0.20/0.58    r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~spl9_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f104])).
% 0.20/0.58  fof(f201,plain,(
% 0.20/0.58    m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1) | spl9_1),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f111,f114,f113,f129,f180])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    ( ! [X31,X32] : (~m1_subset_1(X32,k2_struct_0(sK0)) | m1_connsp_2(X31,sK0,X32) | ~r2_hidden(X32,X31) | ~v3_pre_topc(X31,sK0) | ~m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f179,f55])).
% 0.20/0.58  fof(f179,plain,(
% 0.20/0.58    ( ! [X31,X32] : (~m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X31,sK0,X32) | ~r2_hidden(X32,X31) | ~v3_pre_topc(X31,sK0) | ~m1_subset_1(X32,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f178,f56])).
% 0.20/0.58  fof(f178,plain,(
% 0.20/0.58    ( ! [X31,X32] : (~m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X31,sK0,X32) | ~r2_hidden(X32,X31) | ~v3_pre_topc(X31,sK0) | ~m1_subset_1(X32,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f151,f57])).
% 0.20/0.58  fof(f151,plain,(
% 0.20/0.58    ( ! [X31,X32] : (~m1_subset_1(X31,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X31,sK0,X32) | ~r2_hidden(X32,X31) | ~v3_pre_topc(X31,sK0) | ~m1_subset_1(X32,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(superposition,[],[f73,f128])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_1),
% 0.20/0.58    inference(backward_demodulation,[],[f112,f128])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl9_1),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f56,f57,f102,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f45])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    v3_pre_topc(sK4(sK0,sK2,sK1),sK0) | spl9_1),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f56,f57,f102,f76])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK4(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f45])).
% 0.20/0.58  fof(f114,plain,(
% 0.20/0.58    r2_hidden(sK1,sK4(sK0,sK2,sK1)) | spl9_1),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f56,f57,f102,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK4(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f45])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    spl9_1 | spl9_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f61,f104,f100])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    ~spl9_1 | ~spl9_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f62,f104,f100])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (952)------------------------------
% 0.20/0.58  % (952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (952)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (952)Memory used [KB]: 10874
% 0.20/0.58  % (952)Time elapsed: 0.153 s
% 0.20/0.58  % (952)------------------------------
% 0.20/0.58  % (952)------------------------------
% 0.20/0.58  % (922)Success in time 0.221 s
%------------------------------------------------------------------------------
