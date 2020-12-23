%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2021+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:03 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  115 (1309 expanded)
%              Number of leaves         :   16 ( 514 expanded)
%              Depth                    :   33
%              Number of atoms          :  378 (9546 expanded)
%              Number of equality atoms :   58 (2535 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f224,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X1)
                & v2_tops_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,sK1)
              & v2_tops_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,sK1)
            & v2_tops_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK1)
          & v2_tops_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK1)
        & v2_tops_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ v2_tops_2(sK3,sK1)
      & v2_tops_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_9)).

% (5323)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f224,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f223,f92])).

fof(f92,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f88,f42])).

fof(f42,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f74,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X6,X4,X5] :
      ( ~ l1_pre_topc(X4)
      | u1_struct_0(X4) = X5
      | g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) != g1_pre_topc(X5,X6) ) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f223,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f222,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f222,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f220,f62])).

fof(f62,plain,(
    ~ v2_tops_2(sK2,sK1) ),
    inference(backward_demodulation,[],[f45,f43])).

fof(f43,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f220,plain,
    ( v2_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f217,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f217,plain,(
    v4_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f215,f156])).

fof(f156,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f155,f40])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(sK1,sK2),X0) ) ),
    inference(resolution,[],[f154,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f154,plain,(
    r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f150,f62])).

fof(f150,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | v2_tops_2(sK2,sK1) ),
    inference(resolution,[],[f141,f40])).

fof(f141,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK4(sK1,X1),X1)
      | v2_tops_2(X1,sK1) ) ),
    inference(forward_demodulation,[],[f140,f92])).

fof(f140,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | v2_tops_2(X1,sK1) ) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f215,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f214,f189])).

fof(f189,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f188,f92])).

fof(f188,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f187,f92])).

fof(f187,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),u1_struct_0(sK0),X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f185,f95])).

fof(f95,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f66,f92])).

fof(f66,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f46,f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f185,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f214,plain,(
    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f208,f213])).

fof(f213,plain,(
    m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f211,f38])).

fof(f211,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f210,f49])).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),X0) ) ),
    inference(resolution,[],[f207,f61])).

fof(f207,plain,(
    r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f206,f70])).

fof(f70,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f68,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f67,f65])).

fof(f65,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f64,f38])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f47,f48])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

% (5327)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f206,plain,
    ( r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f204,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f204,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f203,f38])).

fof(f203,plain,
    ( r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f201,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f201,plain,(
    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),sK0) ),
    inference(forward_demodulation,[],[f200,f65])).

fof(f200,plain,(
    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK4(sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f199,f38])).

fof(f199,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK4(sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f198,f156])).

fof(f198,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK4(sK1,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f197,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f197,plain,(
    v4_pre_topc(sK4(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f196,f156])).

fof(f196,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK4(sK1,sK2),sK0) ),
    inference(resolution,[],[f195,f154])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f194,f38])).

fof(f194,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f40])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f54,f44])).

fof(f44,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_tops_2(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f208,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),sK1) ),
    inference(resolution,[],[f207,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f132,f92])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f130,f39])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f51,f123])).

fof(f123,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(superposition,[],[f111,f93])).

fof(f93,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f42,f92])).

fof(f111,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(resolution,[],[f108,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f49,f92])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
