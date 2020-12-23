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
% DateTime   : Thu Dec  3 13:17:48 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  163 (2427 expanded)
%              Number of leaves         :   19 ( 850 expanded)
%              Depth                    :   46
%              Number of atoms          :  710 (27711 expanded)
%              Number of equality atoms :   69 (4829 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f809,plain,(
    $false ),
    inference(subsumption_resolution,[],[f537,f800])).

fof(f800,plain,(
    ! [X2] : ~ r2_hidden(X2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f795,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f795,plain,(
    v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f794,f82])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f80,f50])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
    & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
          & ~ r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
        & ~ r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
   => ( ( ! [X4] :
            ( sK3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        | ! [X5] :
            ( sK3 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
      & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

% (24028)Termination reason: Refutation not found, incomplete strategy

% (24028)Memory used [KB]: 10746
% (24028)Time elapsed: 0.150 s
% (24028)------------------------------
% (24028)------------------------------
% (24038)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (24043)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (24027)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
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

fof(f794,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f793,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f793,plain,
    ( ~ l1_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f789,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f789,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f787,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f787,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f784,f541])).

fof(f541,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f537,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f784,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f783,f75])).

fof(f75,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X5] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f783,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f779,f64])).

fof(f779,plain,(
    r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f778,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f778,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f777,f46])).

fof(f777,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f776,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f776,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f775,f48])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f775,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f774,f49])).

fof(f774,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f773,f50])).

fof(f773,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f767,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f767,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f759,f529])).

fof(f529,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f528,f169])).

fof(f169,plain,(
    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f150,f80])).

fof(f150,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f148,f49])).

fof(f148,plain,
    ( v2_struct_0(sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f143,f50])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f142,f45])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f46])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f528,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f492,f54])).

fof(f492,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f59,f457])).

fof(f457,plain,(
    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f456,f49])).

fof(f456,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f455,f50])).

fof(f455,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f245,f51])).

fof(f51,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f245,plain,(
    ! [X0] :
      ( r1_tsep_1(sK1,X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f244,f45])).

fof(f244,plain,(
    ! [X0] :
      ( r1_tsep_1(sK1,X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f243,f46])).

fof(f243,plain,(
    ! [X0] :
      ( r1_tsep_1(sK1,X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f47])).

fof(f237,plain,(
    ! [X0] :
      ( r1_tsep_1(sK1,X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f48])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f78,f71])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f77,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f76,f73])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f759,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f747,f546])).

fof(f546,plain,(
    m1_subset_1(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f545,f46])).

fof(f545,plain,
    ( m1_subset_1(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f491,f150])).

fof(f491,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X4)
      | m1_subset_1(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f56,f457])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f747,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK3,u1_struct_0(sK2))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f745,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f745,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f744,f45])).

fof(f744,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f743,f46])).

fof(f743,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f742,f47])).

fof(f742,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f741,f48])).

fof(f741,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f740,f49])).

fof(f740,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f739,f50])).

fof(f739,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f735,f71])).

fof(f735,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f734,f529])).

fof(f734,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f726,f48])).

fof(f726,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(resolution,[],[f665,f475])).

fof(f475,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f459,f457])).

fof(f459,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f85,f457])).

fof(f85,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f665,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(u1_struct_0(X3),u1_struct_0(sK2)))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X3,sK0)
      | r2_hidden(X4,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f649,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f649,plain,(
    ! [X7] :
      ( m1_subset_1(k3_xboole_0(u1_struct_0(X7),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_pre_topc(X7,sK0)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f648,f138])).

fof(f138,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,u1_struct_0(sK2)) = k3_xboole_0(X1,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),X1,u1_struct_0(sK2)) = k3_xboole_0(X1,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f88,f50])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | k9_subset_1(u1_struct_0(X0),X1,u1_struct_0(X2)) = k3_xboole_0(X1,u1_struct_0(X2))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f648,plain,(
    ! [X7] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X7),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_pre_topc(X7,sK0)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f636,f98])).

fof(f98,plain,(
    u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) ),
    inference(resolution,[],[f90,f50])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f636,plain,(
    ! [X7] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X7),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2)))))
      | ~ m1_pre_topc(X7,sK0)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f553,f118])).

fof(f118,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f112,f64])).

fof(f112,plain,
    ( r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f87,f50])).

fof(f87,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | r2_hidden(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(resolution,[],[f56,f63])).

fof(f553,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0))))
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f547,f46])).

fof(f547,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0))))
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f162,f56])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))) ) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

fof(f537,plain,(
    r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f536,f45])).

fof(f536,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f535,f46])).

fof(f535,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f534,f47])).

fof(f534,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f533,f48])).

fof(f533,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f532,f49])).

fof(f532,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f531,f50])).

fof(f531,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f530,f71])).

fof(f530,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f529,f512])).

fof(f512,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f476,f62])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f476,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
      | r2_hidden(sK3,X0) ) ),
    inference(forward_demodulation,[],[f460,f457])).

fof(f460,plain,(
    ! [X0] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
      | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(backward_demodulation,[],[f91,f457])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0)
      | r2_hidden(sK3,X0)
      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    inference(resolution,[],[f85,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (24033)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (24025)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (24030)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.54  % (24021)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.44/0.54  % (24018)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.54  % (24040)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  % (24032)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.55  % (24036)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.55  % (24020)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.55  % (24023)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.56  % (24041)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.56  % (24024)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.56  % (24029)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (24029)Refutation not found, incomplete strategy% (24029)------------------------------
% 1.53/0.56  % (24029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (24019)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.53/0.56  % (24029)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (24029)Memory used [KB]: 10618
% 1.53/0.56  % (24029)Time elapsed: 0.158 s
% 1.53/0.56  % (24029)------------------------------
% 1.53/0.56  % (24029)------------------------------
% 1.53/0.56  % (24042)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.57  % (24039)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.53/0.57  % (24034)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.57  % (24045)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.57  % (24047)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.58  % (24026)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.58  % (24028)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.58  % (24037)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.58  % (24046)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.58  % (24044)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.58  % (24028)Refutation not found, incomplete strategy% (24028)------------------------------
% 1.53/0.58  % (24028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (24022)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.58  % (24035)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.59  % (24025)Refutation found. Thanks to Tanya!
% 1.53/0.59  % SZS status Theorem for theBenchmark
% 1.53/0.59  % SZS output start Proof for theBenchmark
% 1.53/0.59  fof(f809,plain,(
% 1.53/0.59    $false),
% 1.53/0.59    inference(subsumption_resolution,[],[f537,f800])).
% 1.53/0.59  fof(f800,plain,(
% 1.53/0.59    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK1))) )),
% 1.53/0.59    inference(resolution,[],[f795,f69])).
% 1.53/0.59  fof(f69,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f34])).
% 1.53/0.59  fof(f34,plain,(
% 1.53/0.59    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.53/0.59    inference(ennf_transformation,[],[f3])).
% 1.53/0.59  fof(f3,axiom,(
% 1.53/0.59    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 1.53/0.59  fof(f795,plain,(
% 1.53/0.59    v1_xboole_0(u1_struct_0(sK1))),
% 1.53/0.59    inference(subsumption_resolution,[],[f794,f82])).
% 1.53/0.59  fof(f82,plain,(
% 1.53/0.59    l1_pre_topc(sK2)),
% 1.53/0.59    inference(resolution,[],[f80,f50])).
% 1.53/0.59  fof(f50,plain,(
% 1.53/0.59    m1_pre_topc(sK2,sK0)),
% 1.53/0.59    inference(cnf_transformation,[],[f42])).
% 1.53/0.59  fof(f42,plain,(
% 1.53/0.59    ((((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.53/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f41,f40,f39,f38])).
% 1.53/0.59  fof(f38,plain,(
% 1.53/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f39,plain,(
% 1.53/0.59    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f40,plain,(
% 1.53/0.59    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f41,plain,(
% 1.53/0.59    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) => ((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  % (24028)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (24028)Memory used [KB]: 10746
% 1.53/0.59  % (24028)Time elapsed: 0.150 s
% 1.53/0.59  % (24028)------------------------------
% 1.53/0.59  % (24028)------------------------------
% 1.53/0.59  % (24038)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.59  % (24043)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.60  % (24027)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.60  fof(f21,plain,(
% 1.53/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.60    inference(flattening,[],[f20])).
% 1.53/0.60  fof(f20,plain,(
% 1.53/0.60    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f19])).
% 1.53/0.60  fof(f19,plain,(
% 1.53/0.60    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.53/0.60    inference(pure_predicate_removal,[],[f17])).
% 1.53/0.60  fof(f17,plain,(
% 1.53/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.53/0.60    inference(rectify,[],[f16])).
% 1.53/0.60  fof(f16,negated_conjecture,(
% 1.53/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.53/0.60    inference(negated_conjecture,[],[f15])).
% 1.53/0.60  fof(f15,conjecture,(
% 1.53/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.53/0.60  fof(f80,plain,(
% 1.53/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.53/0.60    inference(resolution,[],[f55,f46])).
% 1.53/0.60  fof(f46,plain,(
% 1.53/0.60    l1_pre_topc(sK0)),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f55,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f23])).
% 1.53/0.60  fof(f23,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.60    inference(ennf_transformation,[],[f8])).
% 1.53/0.60  fof(f8,axiom,(
% 1.53/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.53/0.60  fof(f794,plain,(
% 1.53/0.60    v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK2)),
% 1.53/0.60    inference(resolution,[],[f793,f54])).
% 1.53/0.60  fof(f54,plain,(
% 1.53/0.60    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f22])).
% 1.53/0.60  fof(f22,plain,(
% 1.53/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.60    inference(ennf_transformation,[],[f7])).
% 1.53/0.60  fof(f7,axiom,(
% 1.53/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.53/0.60  fof(f793,plain,(
% 1.53/0.60    ~l1_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK1))),
% 1.53/0.60    inference(subsumption_resolution,[],[f789,f49])).
% 1.53/0.60  fof(f49,plain,(
% 1.53/0.60    ~v2_struct_0(sK2)),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f789,plain,(
% 1.53/0.60    v1_xboole_0(u1_struct_0(sK1)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 1.53/0.60    inference(resolution,[],[f787,f59])).
% 1.53/0.60  fof(f59,plain,(
% 1.53/0.60    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f28])).
% 1.53/0.60  fof(f28,plain,(
% 1.53/0.60    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.60    inference(flattening,[],[f27])).
% 1.53/0.60  fof(f27,plain,(
% 1.53/0.60    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f9])).
% 1.53/0.60  fof(f9,axiom,(
% 1.53/0.60    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.53/0.60  fof(f787,plain,(
% 1.53/0.60    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.53/0.60    inference(resolution,[],[f784,f541])).
% 1.53/0.60  fof(f541,plain,(
% 1.53/0.60    m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.53/0.60    inference(resolution,[],[f537,f64])).
% 1.53/0.60  fof(f64,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f44])).
% 1.53/0.60  fof(f44,plain,(
% 1.53/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.53/0.60    inference(nnf_transformation,[],[f31])).
% 1.53/0.60  fof(f31,plain,(
% 1.53/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f4])).
% 1.53/0.60  fof(f4,axiom,(
% 1.53/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.53/0.60  fof(f784,plain,(
% 1.53/0.60    ~m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.53/0.60    inference(resolution,[],[f783,f75])).
% 1.53/0.60  fof(f75,plain,(
% 1.53/0.60    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.53/0.60    inference(equality_resolution,[],[f74])).
% 1.53/0.60  fof(f74,plain,(
% 1.53/0.60    ( ! [X5] : (~m1_subset_1(sK3,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.53/0.60    inference(equality_resolution,[],[f53])).
% 1.53/0.60  fof(f53,plain,(
% 1.53/0.60    ( ! [X4,X5] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f783,plain,(
% 1.53/0.60    m1_subset_1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.53/0.60    inference(resolution,[],[f779,f64])).
% 1.53/0.60  fof(f779,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2))),
% 1.53/0.60    inference(subsumption_resolution,[],[f778,f45])).
% 1.53/0.60  fof(f45,plain,(
% 1.53/0.60    ~v2_struct_0(sK0)),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f778,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f777,f46])).
% 1.53/0.60  fof(f777,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f776,f47])).
% 1.53/0.60  fof(f47,plain,(
% 1.53/0.60    ~v2_struct_0(sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f776,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f775,f48])).
% 1.53/0.60  fof(f48,plain,(
% 1.53/0.60    m1_pre_topc(sK1,sK0)),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f775,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f774,f49])).
% 1.53/0.60  fof(f774,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f773,f50])).
% 1.53/0.60  fof(f773,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(resolution,[],[f767,f71])).
% 1.53/0.60  fof(f71,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f37])).
% 1.53/0.60  fof(f37,plain,(
% 1.53/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.60    inference(flattening,[],[f36])).
% 1.53/0.60  fof(f36,plain,(
% 1.53/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f13])).
% 1.53/0.60  fof(f13,axiom,(
% 1.53/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.53/0.60  fof(f767,plain,(
% 1.53/0.60    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.53/0.60    inference(resolution,[],[f759,f529])).
% 1.53/0.60  fof(f529,plain,(
% 1.53/0.60    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.53/0.60    inference(subsumption_resolution,[],[f528,f169])).
% 1.53/0.60  fof(f169,plain,(
% 1.53/0.60    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.53/0.60    inference(resolution,[],[f150,f80])).
% 1.53/0.60  fof(f150,plain,(
% 1.53/0.60    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f148,f49])).
% 1.53/0.60  fof(f148,plain,(
% 1.53/0.60    v2_struct_0(sK2) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.53/0.60    inference(resolution,[],[f143,f50])).
% 1.53/0.60  fof(f143,plain,(
% 1.53/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f142,f45])).
% 1.53/0.60  fof(f142,plain,(
% 1.53/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f141,f46])).
% 1.53/0.60  fof(f141,plain,(
% 1.53/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f139,f47])).
% 1.53/0.60  fof(f139,plain,(
% 1.53/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.53/0.60    inference(resolution,[],[f73,f48])).
% 1.53/0.60  fof(f73,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f37])).
% 1.53/0.60  fof(f528,plain,(
% 1.53/0.60    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.53/0.60    inference(resolution,[],[f492,f54])).
% 1.53/0.60  fof(f492,plain,(
% 1.53/0.60    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.53/0.60    inference(superposition,[],[f59,f457])).
% 1.53/0.60  fof(f457,plain,(
% 1.53/0.60    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.53/0.60    inference(subsumption_resolution,[],[f456,f49])).
% 1.53/0.60  fof(f456,plain,(
% 1.53/0.60    v2_struct_0(sK2) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.53/0.60    inference(subsumption_resolution,[],[f455,f50])).
% 1.53/0.60  fof(f455,plain,(
% 1.53/0.60    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.53/0.60    inference(resolution,[],[f245,f51])).
% 1.53/0.60  fof(f51,plain,(
% 1.53/0.60    ~r1_tsep_1(sK1,sK2)),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f245,plain,(
% 1.53/0.60    ( ! [X0] : (r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0))) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f244,f45])).
% 1.53/0.60  fof(f244,plain,(
% 1.53/0.60    ( ! [X0] : (r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0)) | v2_struct_0(sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f243,f46])).
% 1.53/0.60  fof(f243,plain,(
% 1.53/0.60    ( ! [X0] : (r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f237,f47])).
% 1.53/0.60  fof(f237,plain,(
% 1.53/0.60    ( ! [X0] : (r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.53/0.60    inference(resolution,[],[f79,f48])).
% 1.53/0.60  fof(f79,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f78,f71])).
% 1.53/0.60  fof(f78,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f77,f72])).
% 1.53/0.60  fof(f72,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f37])).
% 1.53/0.60  fof(f77,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f76,f73])).
% 1.53/0.60  fof(f76,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(equality_resolution,[],[f60])).
% 1.53/0.60  fof(f60,plain,(
% 1.53/0.60    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f43])).
% 1.53/0.60  fof(f43,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.60    inference(nnf_transformation,[],[f30])).
% 1.53/0.60  fof(f30,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.60    inference(flattening,[],[f29])).
% 1.53/0.60  fof(f29,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f12])).
% 1.53/0.60  fof(f12,axiom,(
% 1.53/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.53/0.60  fof(f759,plain,(
% 1.53/0.60    v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.53/0.60    inference(resolution,[],[f747,f546])).
% 1.53/0.60  fof(f546,plain,(
% 1.53/0.60    m1_subset_1(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.60    inference(subsumption_resolution,[],[f545,f46])).
% 1.53/0.60  fof(f545,plain,(
% 1.53/0.60    m1_subset_1(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.53/0.60    inference(resolution,[],[f491,f150])).
% 1.53/0.60  fof(f491,plain,(
% 1.53/0.60    ( ! [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X4) | m1_subset_1(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4)) )),
% 1.53/0.60    inference(superposition,[],[f56,f457])).
% 1.53/0.60  fof(f56,plain,(
% 1.53/0.60    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f24])).
% 1.53/0.60  fof(f24,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.60    inference(ennf_transformation,[],[f14])).
% 1.53/0.60  fof(f14,axiom,(
% 1.53/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.53/0.60  fof(f747,plain,(
% 1.53/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(X1)) )),
% 1.53/0.60    inference(resolution,[],[f745,f65])).
% 1.53/0.60  fof(f65,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f44])).
% 1.53/0.60  fof(f745,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.53/0.60    inference(subsumption_resolution,[],[f744,f45])).
% 1.53/0.60  fof(f744,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f743,f46])).
% 1.53/0.60  fof(f743,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f742,f47])).
% 1.53/0.60  fof(f742,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f741,f48])).
% 1.53/0.60  fof(f741,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f740,f49])).
% 1.53/0.60  fof(f740,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f739,f50])).
% 1.53/0.60  fof(f739,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(resolution,[],[f735,f71])).
% 1.53/0.60  fof(f735,plain,(
% 1.53/0.60    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.53/0.60    inference(resolution,[],[f734,f529])).
% 1.53/0.60  fof(f734,plain,(
% 1.53/0.60    v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.60    inference(subsumption_resolution,[],[f726,f48])).
% 1.53/0.60  fof(f726,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.53/0.60    inference(resolution,[],[f665,f475])).
% 1.53/0.60  fof(f475,plain,(
% 1.53/0.60    r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.53/0.60    inference(forward_demodulation,[],[f459,f457])).
% 1.53/0.60  fof(f459,plain,(
% 1.53/0.60    r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.53/0.60    inference(backward_demodulation,[],[f85,f457])).
% 1.53/0.60  fof(f85,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.53/0.60    inference(resolution,[],[f63,f52])).
% 1.53/0.60  fof(f52,plain,(
% 1.53/0.60    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.53/0.60    inference(cnf_transformation,[],[f42])).
% 1.53/0.60  fof(f63,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f44])).
% 1.53/0.60  fof(f665,plain,(
% 1.53/0.60    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(u1_struct_0(X3),u1_struct_0(sK2))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X3,sK0) | r2_hidden(X4,u1_struct_0(sK2))) )),
% 1.53/0.60    inference(resolution,[],[f649,f67])).
% 1.53/0.60  fof(f67,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f32])).
% 1.53/0.60  fof(f32,plain,(
% 1.53/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f5])).
% 1.53/0.60  fof(f5,axiom,(
% 1.53/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.53/0.60  fof(f649,plain,(
% 1.53/0.60    ( ! [X7] : (m1_subset_1(k3_xboole_0(u1_struct_0(X7),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(X7,sK0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.53/0.60    inference(forward_demodulation,[],[f648,f138])).
% 1.53/0.60  fof(f138,plain,(
% 1.53/0.60    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,u1_struct_0(sK2)) = k3_xboole_0(X1,u1_struct_0(sK2))) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f136,f46])).
% 1.53/0.60  fof(f136,plain,(
% 1.53/0.60    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,u1_struct_0(sK2)) = k3_xboole_0(X1,u1_struct_0(sK2)) | ~l1_pre_topc(sK0)) )),
% 1.53/0.60    inference(resolution,[],[f88,f50])).
% 1.53/0.60  fof(f88,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | k9_subset_1(u1_struct_0(X0),X1,u1_struct_0(X2)) = k3_xboole_0(X1,u1_struct_0(X2)) | ~l1_pre_topc(X0)) )),
% 1.53/0.60    inference(resolution,[],[f70,f56])).
% 1.53/0.60  fof(f70,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f35])).
% 1.53/0.60  fof(f35,plain,(
% 1.53/0.60    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f6])).
% 1.53/0.60  fof(f6,axiom,(
% 1.53/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.53/0.60  fof(f648,plain,(
% 1.53/0.60    ( ! [X7] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X7),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(X7,sK0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.53/0.60    inference(forward_demodulation,[],[f636,f98])).
% 1.53/0.60  fof(f98,plain,(
% 1.53/0.60    u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2)))),
% 1.53/0.60    inference(subsumption_resolution,[],[f96,f46])).
% 1.53/0.60  fof(f96,plain,(
% 1.53/0.60    ~l1_pre_topc(sK0) | u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2)))),
% 1.53/0.60    inference(resolution,[],[f90,f50])).
% 1.53/0.60  fof(f90,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1)))) )),
% 1.53/0.60    inference(duplicate_literal_removal,[],[f89])).
% 1.53/0.60  fof(f89,plain,(
% 1.53/0.60    ( ! [X0,X1] : (u1_struct_0(X1) = u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.60    inference(resolution,[],[f57,f56])).
% 1.53/0.60  fof(f57,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f25,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.60    inference(ennf_transformation,[],[f10])).
% 1.53/0.60  fof(f10,axiom,(
% 1.53/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.53/0.60  fof(f636,plain,(
% 1.53/0.60    ( ! [X7] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X7),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))))) | ~m1_pre_topc(X7,sK0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.53/0.60    inference(resolution,[],[f553,f118])).
% 1.53/0.60  fof(f118,plain,(
% 1.53/0.60    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.60    inference(duplicate_literal_removal,[],[f117])).
% 1.53/0.60  fof(f117,plain,(
% 1.53/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.60    inference(resolution,[],[f112,f64])).
% 1.53/0.60  fof(f112,plain,(
% 1.53/0.60    r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.60    inference(subsumption_resolution,[],[f110,f46])).
% 1.53/0.60  fof(f110,plain,(
% 1.53/0.60    ~l1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.60    inference(resolution,[],[f87,f50])).
% 1.53/0.60  fof(f87,plain,(
% 1.53/0.60    ( ! [X4,X3] : (~m1_pre_topc(X3,X4) | ~l1_pre_topc(X4) | r2_hidden(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X4)))) )),
% 1.53/0.60    inference(resolution,[],[f56,f63])).
% 1.53/0.60  fof(f553,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))) | ~m1_pre_topc(X1,sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f547,f46])).
% 1.53/0.60  fof(f547,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k9_subset_1(u1_struct_0(sK0),u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 1.53/0.60    inference(resolution,[],[f162,f56])).
% 1.53/0.60  fof(f162,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0))))) )),
% 1.53/0.60    inference(resolution,[],[f58,f46])).
% 1.53/0.60  fof(f58,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f26])).
% 1.53/0.60  fof(f26,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.60    inference(ennf_transformation,[],[f11])).
% 1.53/0.60  fof(f11,axiom,(
% 1.53/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).
% 1.53/0.60  fof(f537,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1))),
% 1.53/0.60    inference(subsumption_resolution,[],[f536,f45])).
% 1.53/0.60  fof(f536,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f535,f46])).
% 1.53/0.60  fof(f535,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f534,f47])).
% 1.53/0.60  fof(f534,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f533,f48])).
% 1.53/0.60  fof(f533,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f532,f49])).
% 1.53/0.60  fof(f532,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f531,f50])).
% 1.53/0.60  fof(f531,plain,(
% 1.53/0.60    r2_hidden(sK3,u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.53/0.60    inference(resolution,[],[f530,f71])).
% 1.53/0.60  fof(f530,plain,(
% 1.53/0.60    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | r2_hidden(sK3,u1_struct_0(sK1))),
% 1.53/0.60    inference(resolution,[],[f529,f512])).
% 1.53/0.60  fof(f512,plain,(
% 1.53/0.60    v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | r2_hidden(sK3,u1_struct_0(sK1))),
% 1.53/0.60    inference(resolution,[],[f476,f62])).
% 1.53/0.60  fof(f62,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f2])).
% 1.53/0.60  fof(f2,axiom,(
% 1.53/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.53/0.60  fof(f476,plain,(
% 1.53/0.60    ( ! [X0] : (~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X0) | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | r2_hidden(sK3,X0)) )),
% 1.53/0.60    inference(forward_demodulation,[],[f460,f457])).
% 1.53/0.60  fof(f460,plain,(
% 1.53/0.60    ( ! [X0] : (v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0) | r2_hidden(sK3,X0)) )),
% 1.53/0.60    inference(backward_demodulation,[],[f91,f457])).
% 1.53/0.60  fof(f91,plain,(
% 1.53/0.60    ( ! [X0] : (~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0) | r2_hidden(sK3,X0) | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) )),
% 1.53/0.60    inference(resolution,[],[f85,f68])).
% 1.53/0.60  fof(f68,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f33])).
% 1.53/0.60  fof(f33,plain,(
% 1.53/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.53/0.60    inference(ennf_transformation,[],[f18])).
% 1.53/0.60  fof(f18,plain,(
% 1.53/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 1.53/0.60  fof(f1,axiom,(
% 1.53/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.60  % SZS output end Proof for theBenchmark
% 1.53/0.60  % (24025)------------------------------
% 1.53/0.60  % (24025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (24025)Termination reason: Refutation
% 1.53/0.60  
% 1.53/0.60  % (24025)Memory used [KB]: 7419
% 1.53/0.60  % (24025)Time elapsed: 0.148 s
% 1.53/0.60  % (24025)------------------------------
% 1.53/0.60  % (24025)------------------------------
% 1.53/0.61  % (24017)Success in time 0.246 s
%------------------------------------------------------------------------------
