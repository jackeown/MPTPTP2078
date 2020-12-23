%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1128+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:19 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  155 (3413 expanded)
%              Number of leaves         :   20 (1071 expanded)
%              Depth                    :   26
%              Number of atoms          :  513 (10649 expanded)
%              Number of equality atoms :   88 ( 807 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1611,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1610,f1561])).

fof(f1561,plain,(
    r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f1560,f919])).

fof(f919,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f337,f542])).

fof(f542,plain,(
    u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f541,f119])).

fof(f119,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f78,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f78,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f44,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m1_pre_topc(X1,X0)
            & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m1_pre_topc(X1,sK2)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ m1_pre_topc(X1,sK2)
        & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
   => ( ~ m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m1_pre_topc(X1,X0)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
           => m1_pre_topc(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f541,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f540,f118])).

fof(f118,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f78,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f540,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(equality_resolution,[],[f257])).

fof(f257,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
      | u1_struct_0(X0) = u1_struct_0(sK2)
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f116,f51])).

fof(f51,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f116,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_struct_0(sK2) = X0 ) ),
    inference(resolution,[],[f78,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f337,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(subsumption_resolution,[],[f336,f162])).

fof(f162,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f119,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f336,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(superposition,[],[f274,f47])).

fof(f47,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f274,plain,(
    r1_tarski(u1_struct_0(sK3),k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(forward_demodulation,[],[f267,f150])).

fof(f150,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f133,f47])).

fof(f133,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f127,f49])).

fof(f127,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f123,f78])).

fof(f123,plain,
    ( l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f83,f67])).

fof(f83,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f45,plain,(
    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f267,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(resolution,[],[f263,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & ( ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0))
              & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f263,plain,(
    sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f136,f119])).

fof(f136,plain,
    ( sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f134,f127])).

fof(f134,plain,
    ( sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f84,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f84,plain,
    ( ~ sP1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f1560,plain,
    ( r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f1553])).

fof(f1553,plain,
    ( r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f1532,f549])).

fof(f549,plain,
    ( r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f146,f150])).

fof(f146,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f140,f81])).

fof(f81,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f79,f47])).

fof(f79,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f44,f49])).

fof(f140,plain,
    ( r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f137,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f137,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f94,f127])).

fof(f94,plain,
    ( ~ sP0(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f82,f75])).

fof(f75,plain,(
    ! [X1] :
      ( sP1(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f44,f64])).

fof(f82,plain,
    ( ~ sP1(sK2,sK3)
    | ~ sP0(sK3,sK2) ),
    inference(resolution,[],[f46,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ~ m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f1532,plain,
    ( ~ r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(duplicate_literal_removal,[],[f1528])).

fof(f1528,plain,
    ( r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(superposition,[],[f1510,f1512])).

fof(f1512,plain,
    ( sK4(sK3,sK2) = k3_xboole_0(sK5(sK3,sK2),u1_struct_0(sK3))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f1506,f919])).

fof(f1506,plain,
    ( sK4(sK3,sK2) = k3_xboole_0(sK5(sK3,sK2),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(backward_demodulation,[],[f697,f359])).

fof(f359,plain,(
    ! [X6] : k9_subset_1(u1_struct_0(sK3),X6,u1_struct_0(sK3)) = k3_xboole_0(X6,u1_struct_0(sK3)) ),
    inference(resolution,[],[f288,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f288,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f149,f150])).

fof(f149,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f697,plain,
    ( sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f696,f150])).

fof(f696,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),k2_struct_0(sK3))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f147,f150])).

fof(f147,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),k2_struct_0(sK3))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f141,f81])).

fof(f141,plain,
    ( sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),k2_struct_0(sK3))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f137,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK4(X0,X1) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1510,plain,(
    ! [X3] :
      ( r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f1509,f1135])).

fof(f1135,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f1132,f288])).

fof(f1132,plain,(
    ! [X1] :
      ( m1_subset_1(k3_xboole_0(X1,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(superposition,[],[f360,f71])).

fof(f360,plain,(
    ! [X7] : m1_subset_1(k9_subset_1(u1_struct_0(sK3),X7,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f288,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f1509,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k3_xboole_0(X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f1504,f359])).

fof(f1504,plain,(
    ! [X3] :
      ( r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(backward_demodulation,[],[f1072,f359])).

fof(f1072,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X3,u1_pre_topc(sK2))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f1071,f120])).

fof(f120,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X4,u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f78,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f1071,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X3,u1_pre_topc(sK2))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3)) ) ),
    inference(forward_demodulation,[],[f1070,f542])).

fof(f1070,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_pre_topc(sK2))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ) ),
    inference(forward_demodulation,[],[f277,f548])).

fof(f548,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f547,f119])).

fof(f547,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f546,f118])).

fof(f546,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(equality_resolution,[],[f261])).

fof(f261,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
      | u1_pre_topc(X0) = u1_pre_topc(sK2)
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f117,f51])).

fof(f117,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X3,X2)
      | u1_pre_topc(sK2) = X2 ) ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f277,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ) ),
    inference(forward_demodulation,[],[f276,f150])).

fof(f276,plain,(
    ! [X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(forward_demodulation,[],[f271,f150])).

fof(f271,plain,(
    ! [X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f263,f73])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1610,plain,(
    ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(equality_resolution,[],[f1609])).

fof(f1609,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != X0
      | ~ r2_hidden(X0,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f1552,f1561])).

fof(f1552,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != X0
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f1551,f1030])).

fof(f1030,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),u1_pre_topc(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f1012,f282])).

fof(f282,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X4,u1_pre_topc(sK3)) ) ),
    inference(resolution,[],[f132,f72])).

fof(f132,plain,(
    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(resolution,[],[f127,f50])).

fof(f1012,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),u1_pre_topc(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(backward_demodulation,[],[f269,f548])).

fof(f269,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f263,f56])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1551,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != X0
      | ~ r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),u1_pre_topc(sK2))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK3)) ) ),
    inference(superposition,[],[f1511,f1513])).

fof(f1513,plain,(
    ! [X2] :
      ( k3_xboole_0(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2),u1_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f1507,f282])).

fof(f1507,plain,(
    ! [X2] :
      ( k3_xboole_0(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2),u1_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(backward_demodulation,[],[f275,f359])).

fof(f275,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2),u1_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(forward_demodulation,[],[f270,f150])).

fof(f270,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2),k2_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f263,f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1511,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != k3_xboole_0(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f1505,f919])).

fof(f1505,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != k3_xboole_0(X0,u1_struct_0(sK3))
      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ) ),
    inference(backward_demodulation,[],[f864,f359])).

fof(f864,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != k9_subset_1(u1_struct_0(sK3),X0,u1_struct_0(sK3))
      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ) ),
    inference(forward_demodulation,[],[f863,f150])).

fof(f863,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
      | sK4(sK3,sK2) != k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ) ),
    inference(forward_demodulation,[],[f862,f150])).

fof(f862,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
      | sK4(sK3,sK2) != k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f148,f120])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
      | sK4(sK3,sK2) != k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ) ),
    inference(forward_demodulation,[],[f142,f81])).

fof(f142,plain,(
    ! [X0] :
      ( sK4(sK3,sK2) != k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
      | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f137,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

%------------------------------------------------------------------------------
