%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:50 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   98 (2273 expanded)
%              Number of leaves         :   17 ( 949 expanded)
%              Depth                    :   19
%              Number of atoms          :  392 (17525 expanded)
%              Number of equality atoms :   67 (4434 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(subsumption_resolution,[],[f308,f176])).

fof(f176,plain,(
    m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f46,f42,f104,f154,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
                    & v3_pre_topc(sK5(X0,X1,X4),X0)
                    & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
        & v3_pre_topc(sK5(X0,X1,X4),X0)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

% (28092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f154,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f106,f143])).

fof(f143,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f110,f135,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f135,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f131,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

% (28088)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f131,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f127,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f127,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f40,f96,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f96,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f94,f44])).

fof(f44,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v2_tex_2(sK3,sK1)
    & v2_tex_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tex_2(X3,X1)
                    & v2_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tex_2(X3,X1)
                & v2_tex_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tex_2(X3,sK1)
              & v2_tex_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tex_2(X3,sK1)
            & v2_tex_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ v2_tex_2(X3,sK1)
          & v2_tex_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ v2_tex_2(X3,sK1)
        & v2_tex_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v2_tex_2(sK3,sK1)
      & v2_tex_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

fof(f94,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f41,f73,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f73,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f41,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f101,f60])).

fof(f101,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f41,f98,f57])).

fof(f98,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f93,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f85,f41])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f54,f44])).

fof(f93,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f72,f92])).

fof(f72,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f40,f66])).

fof(f106,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f41,f70,f71,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f43,f45])).

fof(f45,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(forward_demodulation,[],[f47,f45])).

fof(f47,plain,(
    ~ v2_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,(
    r1_tarski(sK4(sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f70,f71,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK4(X0,X1),X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f308,plain,(
    ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f307,f143])).

fof(f307,plain,(
    ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f40,f127,f177,f176,f283,f67])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f283,plain,(
    ~ v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f176,f178,f214])).

fof(f214,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),sK2,X0) != sK4(sK1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f213,f88])).

fof(f88,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f213,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) != sK4(sK1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f212,f143])).

fof(f212,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) != sK4(sK1,sK2)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f142,f143])).

fof(f142,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f141,f41])).

fof(f141,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f140,f71])).

fof(f140,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f137,f70])).

fof(f137,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2)
      | v2_tex_2(sK2,sK1)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f53,f89])).

fof(f89,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK1),X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f71,f58])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f178,plain,(
    sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f40,f46,f42,f104,f154,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f177,plain,(
    v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f46,f42,f104,f154,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | v3_pre_topc(sK5(X0,X1,X4),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (28079)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (28084)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (28085)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (28074)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (28075)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (28077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (28083)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (28087)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (28095)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (28094)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (28091)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (28076)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (28097)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.29/0.53  % (28093)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.29/0.53  % (28086)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.29/0.53  % (28096)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.29/0.53  % (28089)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.29/0.53  % (28080)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.29/0.54  % (28080)Refutation not found, incomplete strategy% (28080)------------------------------
% 1.29/0.54  % (28080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (28080)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (28080)Memory used [KB]: 10746
% 1.29/0.54  % (28080)Time elapsed: 0.120 s
% 1.29/0.54  % (28080)------------------------------
% 1.29/0.54  % (28080)------------------------------
% 1.29/0.54  % (28099)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.29/0.54  % (28081)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.29/0.54  % (28098)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.29/0.54  % (28081)Refutation not found, incomplete strategy% (28081)------------------------------
% 1.29/0.54  % (28081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (28081)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (28081)Memory used [KB]: 1791
% 1.29/0.54  % (28081)Time elapsed: 0.098 s
% 1.29/0.54  % (28081)------------------------------
% 1.29/0.54  % (28081)------------------------------
% 1.47/0.54  % (28074)Refutation found. Thanks to Tanya!
% 1.47/0.54  % SZS status Theorem for theBenchmark
% 1.47/0.54  % SZS output start Proof for theBenchmark
% 1.47/0.54  fof(f309,plain,(
% 1.47/0.54    $false),
% 1.47/0.54    inference(subsumption_resolution,[],[f308,f176])).
% 1.47/0.54  fof(f176,plain,(
% 1.47/0.54    m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.54    inference(unit_resulting_resolution,[],[f40,f46,f42,f104,f154,f48])).
% 1.47/0.54  fof(f48,plain,(
% 1.47/0.54    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f35])).
% 1.47/0.54  fof(f35,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 1.47/0.54  fof(f33,plain,(
% 1.47/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.54    introduced(choice_axiom,[])).
% 1.47/0.54  fof(f34,plain,(
% 1.47/0.54    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.54    introduced(choice_axiom,[])).
% 1.47/0.54  % (28092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.47/0.54  fof(f32,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(rectify,[],[f31])).
% 1.47/0.54  fof(f31,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(nnf_transformation,[],[f17])).
% 1.47/0.54  fof(f17,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(flattening,[],[f16])).
% 1.47/0.54  fof(f16,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 1.47/0.55  fof(f154,plain,(
% 1.47/0.55    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.55    inference(backward_demodulation,[],[f106,f143])).
% 1.47/0.55  fof(f143,plain,(
% 1.47/0.55    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f110,f135,f64])).
% 1.47/0.55  fof(f64,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f39])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(flattening,[],[f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(nnf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.55  fof(f135,plain,(
% 1.47/0.55    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f131,f60])).
% 1.47/0.55  fof(f60,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f37])).
% 1.47/0.55  % (28088)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.55    inference(nnf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.55  fof(f131,plain,(
% 1.47/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f127,f57])).
% 1.47/0.55  fof(f57,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f20])).
% 1.47/0.55  fof(f20,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.47/0.55  fof(f127,plain,(
% 1.47/0.55    m1_pre_topc(sK1,sK0)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f96,f54])).
% 1.47/0.55  fof(f54,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f18])).
% 1.47/0.55  fof(f18,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.47/0.55  fof(f96,plain,(
% 1.47/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.47/0.55    inference(forward_demodulation,[],[f94,f44])).
% 1.47/0.55  fof(f44,plain,(
% 1.47/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    (((~v2_tex_2(sK3,sK1) & v2_tex_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    ? [X2] : (? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (~v2_tex_2(sK3,sK1) & v2_tex_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f15,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.47/0.55    inference(flattening,[],[f14])).
% 1.47/0.55  fof(f14,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tex_2(X3,X1) & (v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f13])).
% 1.47/0.55  fof(f13,negated_conjecture,(
% 1.47/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 1.47/0.55    inference(negated_conjecture,[],[f12])).
% 1.47/0.55  fof(f12,conjecture,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f41,f73,f92])).
% 1.47/0.55  fof(f92,plain,(
% 1.47/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f55,f65])).
% 1.47/0.55  fof(f65,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f24])).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f36])).
% 1.47/0.55  fof(f36,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(nnf_transformation,[],[f19])).
% 1.47/0.55  fof(f19,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.47/0.55  fof(f73,plain,(
% 1.47/0.55    m1_pre_topc(sK1,sK1)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f41,f66])).
% 1.47/0.55  fof(f66,plain,(
% 1.47/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f25])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f10])).
% 1.47/0.55  fof(f10,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.47/0.55  fof(f41,plain,(
% 1.47/0.55    l1_pre_topc(sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f110,plain,(
% 1.47/0.55    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f101,f60])).
% 1.47/0.55  fof(f101,plain,(
% 1.47/0.55    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f41,f98,f57])).
% 1.47/0.55  fof(f98,plain,(
% 1.47/0.55    m1_pre_topc(sK0,sK1)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f93,f86])).
% 1.47/0.55  fof(f86,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f85,f41])).
% 1.47/0.55  fof(f85,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 1.47/0.55    inference(superposition,[],[f54,f44])).
% 1.47/0.55  fof(f93,plain,(
% 1.47/0.55    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f72,f92])).
% 1.47/0.55  fof(f72,plain,(
% 1.47/0.55    m1_pre_topc(sK0,sK0)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f66])).
% 1.47/0.55  fof(f106,plain,(
% 1.47/0.55    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f41,f70,f71,f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f35])).
% 1.47/0.55  fof(f71,plain,(
% 1.47/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.47/0.55    inference(forward_demodulation,[],[f43,f45])).
% 1.47/0.55  fof(f45,plain,(
% 1.47/0.55    sK2 = sK3),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f70,plain,(
% 1.47/0.55    ~v2_tex_2(sK2,sK1)),
% 1.47/0.55    inference(forward_demodulation,[],[f47,f45])).
% 1.47/0.55  fof(f47,plain,(
% 1.47/0.55    ~v2_tex_2(sK3,sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f104,plain,(
% 1.47/0.55    r1_tarski(sK4(sK1,sK2),sK2)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f41,f70,f71,f52])).
% 1.47/0.55  fof(f52,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK4(X0,X1),X1) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f35])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f46,plain,(
% 1.47/0.55    v2_tex_2(sK2,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f40,plain,(
% 1.47/0.55    l1_pre_topc(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f308,plain,(
% 1.47/0.55    ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.55    inference(forward_demodulation,[],[f307,f143])).
% 1.47/0.55  fof(f307,plain,(
% 1.47/0.55    ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f127,f177,f176,f283,f67])).
% 1.47/0.55  fof(f67,plain,(
% 1.47/0.55    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(equality_resolution,[],[f59])).
% 1.47/0.55  fof(f59,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f23])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(flattening,[],[f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 1.47/0.55  fof(f283,plain,(
% 1.47/0.55    ~v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f176,f178,f214])).
% 1.47/0.55  fof(f214,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK2,X0) != sK4(sK1,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK1)) )),
% 1.47/0.55    inference(superposition,[],[f213,f88])).
% 1.47/0.55  fof(f88,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)) )),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f42,f58])).
% 1.47/0.55  fof(f58,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f2])).
% 1.47/0.55  fof(f2,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.47/0.55  fof(f213,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) != sK4(sK1,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK1)) )),
% 1.47/0.55    inference(forward_demodulation,[],[f212,f143])).
% 1.47/0.55  fof(f212,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) != sK4(sK1,sK2) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.47/0.55    inference(forward_demodulation,[],[f142,f143])).
% 1.47/0.55  fof(f142,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f141,f41])).
% 1.47/0.55  fof(f141,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f140,f71])).
% 1.47/0.55  fof(f140,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f137,f70])).
% 1.47/0.55  fof(f137,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK1),X0,sK2) != sK4(sK1,sK2) | v2_tex_2(sK2,sK1) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 1.47/0.55    inference(superposition,[],[f53,f89])).
% 1.47/0.55  fof(f89,plain,(
% 1.47/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK1),X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK2,X0)) )),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f71,f58])).
% 1.47/0.55  fof(f53,plain,(
% 1.47/0.55    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | v2_tex_2(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f35])).
% 1.47/0.55  fof(f178,plain,(
% 1.47/0.55    sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2)))),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f46,f42,f104,f154,f50])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f35])).
% 1.47/0.55  fof(f177,plain,(
% 1.47/0.55    v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK0)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f40,f46,f42,f104,f154,f49])).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | v3_pre_topc(sK5(X0,X1,X4),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f35])).
% 1.47/0.55  % SZS output end Proof for theBenchmark
% 1.47/0.55  % (28074)------------------------------
% 1.47/0.55  % (28074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (28074)Termination reason: Refutation
% 1.47/0.55  
% 1.47/0.55  % (28074)Memory used [KB]: 10874
% 1.47/0.55  % (28074)Time elapsed: 0.126 s
% 1.47/0.55  % (28074)------------------------------
% 1.47/0.55  % (28074)------------------------------
% 1.47/0.55  % (28073)Success in time 0.188 s
%------------------------------------------------------------------------------
