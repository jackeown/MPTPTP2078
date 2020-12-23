%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1146+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:21 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  323 (6164151 expanded)
%              Number of leaves         :   22 (2266022 expanded)
%              Depth                    :  136
%              Number of atoms          : 1458 (80034856 expanded)
%              Number of equality atoms :  122 (1190016 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f908,plain,(
    $false ),
    inference(resolution,[],[f906,f893])).

fof(f893,plain,(
    r2_hidden(sK2,sK3) ),
    inference(subsumption_resolution,[],[f892,f866])).

fof(f866,plain,(
    ! [X2] : ~ r2_hidden(X2,u1_orders_2(sK0)) ),
    inference(resolution,[],[f864,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f864,plain,(
    v1_xboole_0(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f862,f59])).

fof(f59,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ( ! [X3] :
            ( ~ r2_hidden(sK2,X3)
            | ~ r2_hidden(sK1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X3,sK0) )
        & ( r1_orders_2(sK0,sK2,sK1)
          | r1_orders_2(sK0,sK1,sK2) ) )
      | ( ~ r1_orders_2(sK0,sK2,sK1)
        & ~ r1_orders_2(sK0,sK1,sK2)
        & r2_hidden(sK2,sK3)
        & r2_hidden(sK1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(sK3,sK0) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ! [X3] :
                        ( ~ r2_hidden(X2,X3)
                        | ~ r2_hidden(X1,X3)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        | ~ v6_orders_2(X3,X0) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                      | ~ v6_orders_2(X3,sK0) )
                  & ( r1_orders_2(sK0,X2,X1)
                    | r1_orders_2(sK0,X1,X2) ) )
                | ( ~ r1_orders_2(sK0,X2,X1)
                  & ~ r1_orders_2(sK0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                      & v6_orders_2(X4,sK0) ) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                    | ~ v6_orders_2(X3,sK0) )
                & ( r1_orders_2(sK0,X2,X1)
                  | r1_orders_2(sK0,X1,X2) ) )
              | ( ~ r1_orders_2(sK0,X2,X1)
                & ~ r1_orders_2(sK0,X1,X2)
                & ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                    & v6_orders_2(X4,sK0) ) ) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r2_hidden(sK1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | ~ v6_orders_2(X3,sK0) )
              & ( r1_orders_2(sK0,X2,sK1)
                | r1_orders_2(sK0,sK1,X2) ) )
            | ( ~ r1_orders_2(sK0,X2,sK1)
              & ~ r1_orders_2(sK0,sK1,X2)
              & ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r2_hidden(sK1,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                  & v6_orders_2(X4,sK0) ) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ( ! [X3] :
                ( ~ r2_hidden(X2,X3)
                | ~ r2_hidden(sK1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(X3,sK0) )
            & ( r1_orders_2(sK0,X2,sK1)
              | r1_orders_2(sK0,sK1,X2) ) )
          | ( ~ r1_orders_2(sK0,X2,sK1)
            & ~ r1_orders_2(sK0,sK1,X2)
            & ? [X4] :
                ( r2_hidden(X2,X4)
                & r2_hidden(sK1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                & v6_orders_2(X4,sK0) ) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ! [X3] :
              ( ~ r2_hidden(sK2,X3)
              | ~ r2_hidden(sK1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | ~ v6_orders_2(X3,sK0) )
          & ( r1_orders_2(sK0,sK2,sK1)
            | r1_orders_2(sK0,sK1,sK2) ) )
        | ( ~ r1_orders_2(sK0,sK2,sK1)
          & ~ r1_orders_2(sK0,sK1,sK2)
          & ? [X4] :
              ( r2_hidden(sK2,X4)
              & r2_hidden(sK1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
              & v6_orders_2(X4,sK0) ) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( r2_hidden(sK2,X4)
        & r2_hidden(sK1,X4)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(X4,sK0) )
   => ( r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      & v6_orders_2(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ~ ( ! [X3] :
                          ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                            & v6_orders_2(X3,X0) )
                         => ~ ( r2_hidden(X2,X3)
                              & r2_hidden(X1,X3) ) )
                      & ( r1_orders_2(X0,X2,X1)
                        | r1_orders_2(X0,X1,X2) ) )
                  & ~ ( ~ r1_orders_2(X0,X2,X1)
                      & ~ r1_orders_2(X0,X1,X2)
                      & ? [X4] :
                          ( r2_hidden(X2,X4)
                          & r2_hidden(X1,X4)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ~ ( ! [X3] :
                          ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                            & v6_orders_2(X3,X0) )
                         => ~ ( r2_hidden(X2,X3)
                              & r2_hidden(X1,X3) ) )
                      & ( r1_orders_2(X0,X2,X1)
                        | r1_orders_2(X0,X1,X2) ) )
                  & ~ ( ~ r1_orders_2(X0,X2,X1)
                      & ~ r1_orders_2(X0,X1,X2)
                      & ? [X3] :
                          ( r2_hidden(X2,X3)
                          & r2_hidden(X1,X3)
                          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f862,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f854,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f854,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f853,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f853,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f852,f59])).

fof(f852,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f851,f79])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

% (10960)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f851,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f848,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f848,plain,(
    v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f844])).

fof(f844,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f842,f823])).

fof(f823,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f822,f783])).

fof(f783,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_orders_2(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f781,f93])).

fof(f781,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f779,f59])).

fof(f779,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f771,f80])).

fof(f771,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
      | v2_struct_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f770,f92])).

fof(f770,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f769,f751])).

fof(f751,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f750,f414])).

fof(f414,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f413,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f413,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f412,f61])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f412,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f97,f406])).

fof(f406,plain,(
    k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(resolution,[],[f369,f246])).

fof(f246,plain,
    ( r2_hidden(sK1,sK3)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f245,f172])).

fof(f172,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_orders_2(sK0))
      | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f170,f93])).

fof(f170,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f168,f59])).

fof(f168,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f134,f80])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
      | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f131,f92])).

fof(f131,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(resolution,[],[f125,f61])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k7_domain_1(u1_struct_0(sK0),sK1,X0) = k2_tarski(sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f98,f60])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f245,plain,
    ( r2_hidden(sK1,sK3)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f244,f61])).

fof(f244,plain,
    ( r2_hidden(sK1,sK3)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f213,f200])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f199,f60])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f81,f59])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f213,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(resolution,[],[f205,f172])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f202,f64])).

fof(f64,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f202,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f201,f60])).

fof(f201,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X1)
      | r2_hidden(k4_tarski(sK2,X1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f199,f61])).

fof(f369,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ) ),
    inference(condensation,[],[f368])).

fof(f368,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(X18,sK3)
      | ~ r2_hidden(X19,sK3)
      | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f367,f172])).

fof(f367,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(X18,sK3)
      | ~ r2_hidden(X19,sK3)
      | r2_hidden(k4_tarski(X18,X19),u1_orders_2(sK0))
      | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f361,f172])).

fof(f361,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(X18,sK3)
      | ~ r2_hidden(X19,sK3)
      | r2_hidden(k4_tarski(X19,X18),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X18,X19),u1_orders_2(sK0))
      | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f319,f339])).

fof(f339,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f338,f172])).

fof(f338,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f337,f61])).

fof(f337,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f335,f200])).

fof(f335,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f334,f172])).

fof(f334,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f308,f202])).

fof(f308,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(resolution,[],[f289,f63])).

fof(f63,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f289,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f286,f59])).

fof(f286,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f280,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v6_orders_2(X1,X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f280,plain,
    ( v6_orders_2(sK3,sK0)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f279,f172])).

fof(f279,plain,
    ( v6_orders_2(sK3,sK0)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f278,f61])).

fof(f278,plain,
    ( v6_orders_2(sK3,sK0)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f217,f200])).

fof(f217,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(resolution,[],[f206,f172])).

fof(f206,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0) ),
    inference(resolution,[],[f202,f62])).

fof(f62,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( ~ r7_relat_2(u1_orders_2(sK0),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f74,f115])).

fof(f115,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f114,f59])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f80,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r7_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X5,X4),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
              & r2_hidden(sK5(X0,X1),X1)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f750,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f749,f106])).

fof(f106,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f749,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f743,f108])).

fof(f108,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f743,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f741,f69])).

fof(f69,plain,(
    ! [X3] :
      ( ~ v6_orders_2(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,X3)
      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f741,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f740,f406])).

fof(f740,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f739,f61])).

fof(f739,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f737])).

fof(f737,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f732,f456])).

fof(f456,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK1,X0)
      | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,X0),sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f455,f60])).

fof(f455,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X0),sK0)
      | v2_struct_0(sK0)
      | ~ r1_orders_2(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f454])).

fof(f454,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X0),sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f453,f349])).

fof(f349,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f348,f59])).

fof(f348,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r3_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f58])).

fof(f58,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f453,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f452,f59])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f58])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                  | ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) ) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                  | ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) ) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_orders_2)).

fof(f732,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f731,f414])).

fof(f731,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f730,f716])).

fof(f716,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f715,f61])).

fof(f715,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f714,f312])).

fof(f312,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(resolution,[],[f311,f60])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r1_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f714,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f692,f314])).

fof(f314,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f313,f60])).

fof(f313,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(sK2,X1),u1_orders_2(sK0))
      | r1_orders_2(sK0,sK2,X1) ) ),
    inference(resolution,[],[f311,f61])).

fof(f692,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f686])).

fof(f686,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f684,f552])).

fof(f552,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f551,f414])).

fof(f551,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f550,f106])).

fof(f550,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f543,f108])).

fof(f543,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f539])).

fof(f539,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f535,f71])).

fof(f71,plain,(
    ! [X3] :
      ( ~ v6_orders_2(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,X3)
      | r2_hidden(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f535,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f534,f406])).

fof(f534,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f533,f61])).

fof(f533,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f531])).

fof(f531,plain,
    ( r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f529,f456])).

fof(f529,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f476,f414])).

fof(f476,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f475,f65])).

fof(f65,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f475,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f474,f106])).

fof(f474,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f466,f108])).

fof(f466,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f462,f73])).

fof(f73,plain,(
    ! [X3] :
      ( ~ v6_orders_2(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,X3)
      | ~ r1_orders_2(sK0,sK2,sK1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f462,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f460,f65])).

fof(f460,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | v2_struct_0(sK0)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f458,f434])).

fof(f434,plain,(
    k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(resolution,[],[f375,f238])).

fof(f238,plain,
    ( r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f237,f190])).

fof(f190,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_orders_2(sK0))
      | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ) ),
    inference(resolution,[],[f188,f93])).

fof(f188,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f186,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f149,f80])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
      | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f146,f92])).

fof(f146,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(forward_demodulation,[],[f144,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f144,plain,
    ( k2_tarski(sK2,sK1) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f126,f60])).

fof(f126,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_domain_1(u1_struct_0(sK0),sK2,X1) = k2_tarski(sK2,X1)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f98,f61])).

fof(f237,plain,
    ( r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f236,f61])).

fof(f236,plain,
    ( r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f211,f200])).

fof(f211,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(resolution,[],[f205,f190])).

fof(f375,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ) ),
    inference(condensation,[],[f374])).

fof(f374,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(X22,sK3)
      | ~ r2_hidden(X23,sK3)
      | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f373,f190])).

fof(f373,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(X22,sK3)
      | ~ r2_hidden(X23,sK3)
      | r2_hidden(k4_tarski(X22,X23),u1_orders_2(sK0))
      | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f363,f190])).

fof(f363,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(X22,sK3)
      | ~ r2_hidden(X23,sK3)
      | r2_hidden(k4_tarski(X23,X22),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X22,X23),u1_orders_2(sK0))
      | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ) ),
    inference(resolution,[],[f319,f325])).

fof(f325,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f324,f190])).

fof(f324,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f323,f61])).

fof(f323,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f321,f200])).

fof(f321,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f320,f190])).

fof(f320,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f304,f202])).

fof(f304,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(resolution,[],[f263,f63])).

fof(f263,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f260,f59])).

fof(f260,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f254,f83])).

fof(f254,plain,
    ( v6_orders_2(sK3,sK0)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f253,f190])).

fof(f253,plain,
    ( v6_orders_2(sK3,sK0)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f252,f61])).

fof(f252,plain,
    ( v6_orders_2(sK3,sK0)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f215,f200])).

fof(f215,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(resolution,[],[f206,f190])).

fof(f458,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK2,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f457,f60])).

fof(f457,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK2,X1),sK0)
      | v2_struct_0(sK0)
      | ~ r1_orders_2(sK0,sK2,X1) ) ),
    inference(resolution,[],[f455,f61])).

fof(f684,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0))
      | r2_hidden(k4_tarski(sK1,X1),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X1,sK1),u1_orders_2(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f680])).

fof(f680,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(X1,sK3)
      | v1_xboole_0(u1_struct_0(sK0))
      | r2_hidden(k4_tarski(sK1,X1),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X1,sK1),u1_orders_2(sK0))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f678,f587])).

fof(f587,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f586,f414])).

fof(f586,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f585,f106])).

fof(f585,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f578,f108])).

fof(f578,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f575])).

fof(f575,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f570,f70])).

fof(f70,plain,(
    ! [X3] :
      ( ~ v6_orders_2(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,X3)
      | r2_hidden(sK1,sK3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f570,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f569,f406])).

fof(f569,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f568,f61])).

fof(f568,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f566])).

fof(f566,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f564,f456])).

fof(f564,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f497,f414])).

fof(f497,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f496,f64])).

fof(f496,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f495,f106])).

fof(f495,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f487,f108])).

fof(f487,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f463,f73])).

fof(f463,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f460,f64])).

fof(f678,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK3)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK3)
      | v1_xboole_0(u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f669,f319])).

fof(f669,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f668,f630])).

fof(f630,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f627,f59])).

fof(f627,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f618,f83])).

fof(f618,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f617,f414])).

fof(f617,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f616,f106])).

fof(f616,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f609,f108])).

fof(f609,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f607])).

fof(f607,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | v6_orders_2(sK3,sK0) ),
    inference(resolution,[],[f601,f68])).

fof(f68,plain,(
    ! [X3] :
      ( ~ v6_orders_2(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,X3)
      | v6_orders_2(sK3,sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f601,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f600,f406])).

fof(f600,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f599,f61])).

fof(f599,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f595,f456])).

fof(f595,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f518,f414])).

fof(f518,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f517,f62])).

fof(f517,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f516,f106])).

fof(f516,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f508,f108])).

fof(f508,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f464,f73])).

fof(f464,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0) ),
    inference(resolution,[],[f460,f62])).

fof(f668,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f667,f414])).

fof(f667,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f666,f106])).

fof(f666,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f660,f108])).

fof(f660,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f658,f69])).

fof(f658,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(forward_demodulation,[],[f657,f406])).

fof(f657,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f656,f61])).

fof(f656,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f645,f456])).

fof(f645,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f644,f630])).

fof(f644,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f643,f414])).

fof(f643,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f642,f106])).

fof(f642,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f636,f108])).

fof(f636,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f635,f69])).

fof(f635,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(duplicate_literal_removal,[],[f633])).

fof(f633,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f632,f460])).

fof(f632,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f630,f63])).

fof(f730,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f729,f106])).

fof(f729,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f721,f108])).

fof(f721,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f719,f73])).

fof(f719,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f717])).

fof(f717,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f716,f460])).

fof(f769,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f768,f618])).

fof(f768,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK3,sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f767,f587])).

fof(f767,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK3,sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f766])).

fof(f766,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK3,sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f736,f552])).

fof(f736,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X0,sK0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f732,f72])).

fof(f72,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0)
      | ~ r2_hidden(sK2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f822,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK2,sK3)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f818,f61])).

fof(f818,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f786,f200])).

fof(f786,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f783,f204])).

fof(f204,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f202,f65])).

fof(f842,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v2_struct_0(sK0) ) ),
    inference(condensation,[],[f841])).

fof(f841,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f840,f783])).

fof(f840,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    inference(subsumption_resolution,[],[f839,f783])).

fof(f839,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f837,f319])).

fof(f837,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f836,f783])).

fof(f836,plain,
    ( v2_struct_0(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f832,f61])).

fof(f832,plain,
    ( v2_struct_0(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f829,f200])).

fof(f829,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f827,f783])).

fof(f827,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f825,f202])).

fof(f825,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(resolution,[],[f807,f63])).

fof(f807,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f806,f59])).

fof(f806,plain,
    ( v2_struct_0(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f800,f83])).

fof(f800,plain,
    ( v6_orders_2(sK3,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f799,f783])).

fof(f799,plain,
    ( v2_struct_0(sK0)
    | v6_orders_2(sK3,sK0)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f795,f61])).

fof(f795,plain,
    ( v2_struct_0(sK0)
    | v6_orders_2(sK3,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f784,f200])).

fof(f784,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | v6_orders_2(sK3,sK0) ),
    inference(resolution,[],[f783,f206])).

fof(f892,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f891,f61])).

fof(f891,plain,
    ( r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f869,f200])).

fof(f869,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f866,f204])).

fof(f906,plain,(
    ! [X0] : ~ r2_hidden(X0,sK3) ),
    inference(condensation,[],[f905])).

fof(f905,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f904,f866])).

fof(f904,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    inference(subsumption_resolution,[],[f903,f866])).

fof(f903,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f901,f319])).

fof(f901,plain,(
    r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f900,f866])).

fof(f900,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f899,f61])).

fof(f899,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f897,f200])).

fof(f897,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f896,f866])).

fof(f896,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f895,f202])).

fof(f895,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(resolution,[],[f885,f63])).

fof(f885,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r7_relat_2(u1_orders_2(sK0),sK3) ),
    inference(subsumption_resolution,[],[f884,f59])).

fof(f884,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f879,f83])).

fof(f879,plain,(
    v6_orders_2(sK3,sK0) ),
    inference(subsumption_resolution,[],[f878,f866])).

fof(f878,plain,
    ( v6_orders_2(sK3,sK0)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f877,f61])).

fof(f877,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f867,f200])).

fof(f867,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0) ),
    inference(resolution,[],[f866,f206])).

%------------------------------------------------------------------------------
