%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 (2862 expanded)
%              Number of leaves         :   17 ( 872 expanded)
%              Depth                    :   32
%              Number of atoms          :  753 (33670 expanded)
%              Number of equality atoms :   36 (2523 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1312,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1311,f416])).

fof(f416,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f399,f59])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_pre_topc(sK3,sK1)
      | ~ v1_tsep_1(sK3,sK1)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ v1_tsep_1(sK2,sK1) )
    & ( ( m1_pre_topc(sK3,sK1)
        & v1_tsep_1(sK3,sK1) )
      | ( m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1) ) )
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK1)
                | ~ v1_tsep_1(X2,sK1)
                | ~ m1_pre_topc(X1,sK1)
                | ~ v1_tsep_1(X1,sK1) )
              & ( ( m1_pre_topc(X2,sK1)
                  & v1_tsep_1(X2,sK1) )
                | ( m1_pre_topc(X1,sK1)
                  & v1_tsep_1(X1,sK1) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK1)
              | ~ v1_tsep_1(X2,sK1)
              | ~ m1_pre_topc(X1,sK1)
              | ~ v1_tsep_1(X1,sK1) )
            & ( ( m1_pre_topc(X2,sK1)
                & v1_tsep_1(X2,sK1) )
              | ( m1_pre_topc(X1,sK1)
                & v1_tsep_1(X1,sK1) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK1)
            | ~ v1_tsep_1(X2,sK1)
            | ~ m1_pre_topc(sK2,sK1)
            | ~ v1_tsep_1(sK2,sK1) )
          & ( ( m1_pre_topc(X2,sK1)
              & v1_tsep_1(X2,sK1) )
            | ( m1_pre_topc(sK2,sK1)
              & v1_tsep_1(sK2,sK1) ) )
          & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK1)
          | ~ v1_tsep_1(X2,sK1)
          | ~ m1_pre_topc(sK2,sK1)
          | ~ v1_tsep_1(sK2,sK1) )
        & ( ( m1_pre_topc(X2,sK1)
            & v1_tsep_1(X2,sK1) )
          | ( m1_pre_topc(sK2,sK1)
            & v1_tsep_1(sK2,sK1) ) )
        & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK3,sK1)
        | ~ v1_tsep_1(sK3,sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | ~ v1_tsep_1(sK2,sK1) )
      & ( ( m1_pre_topc(sK3,sK1)
          & v1_tsep_1(sK3,sK1) )
        | ( m1_pre_topc(sK2,sK1)
          & v1_tsep_1(sK2,sK1) ) )
      & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f399,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f392,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f392,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f387,f59])).

fof(f387,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK2,sK1) ),
    inference(resolution,[],[f316,f68])).

fof(f68,plain,
    ( m1_pre_topc(sK3,sK1)
    | m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f316,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(sK3,X10)
      | m1_pre_topc(sK2,X10)
      | ~ l1_pre_topc(X10) ) ),
    inference(subsumption_resolution,[],[f315,f62])).

fof(f62,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f315,plain,(
    ! [X10] :
      ( m1_pre_topc(sK2,X10)
      | ~ m1_pre_topc(sK3,X10)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(X10) ) ),
    inference(subsumption_resolution,[],[f314,f60])).

fof(f60,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f314,plain,(
    ! [X10] :
      ( m1_pre_topc(sK2,X10)
      | ~ m1_pre_topc(sK3,X10)
      | ~ v2_pre_topc(sK2)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(X10) ) ),
    inference(subsumption_resolution,[],[f313,f61])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f313,plain,(
    ! [X10] :
      ( m1_pre_topc(sK2,X10)
      | ~ m1_pre_topc(sK3,X10)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(X10) ) ),
    inference(subsumption_resolution,[],[f286,f63])).

fof(f63,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f286,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK3)
      | m1_pre_topc(sK2,X10)
      | ~ m1_pre_topc(sK3,X10)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(X10) ) ),
    inference(superposition,[],[f104,f64])).

fof(f64,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f1311,plain,(
    ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f1310,f895])).

fof(f895,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f893,f844])).

fof(f844,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f817,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f817,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f816,f726])).

fof(f726,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK2) ),
    inference(forward_demodulation,[],[f725,f70])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f725,plain,(
    v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f724,f192])).

fof(f192,plain,(
    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f171,f60])).

fof(f171,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f61,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
            & r1_tarski(sK6(X0),u1_pre_topc(X0))
            & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
        & r1_tarski(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f31])).

fof(f31,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f724,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f719,f70])).

fof(f719,plain,
    ( ~ r2_hidden(k2_subset_1(u1_struct_0(sK2)),u1_pre_topc(sK2))
    | v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f181,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f181,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X5,u1_pre_topc(sK2))
      | v3_pre_topc(X5,sK2) ) ),
    inference(resolution,[],[f61,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f816,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f815,f70])).

fof(f815,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f807,f70])).

fof(f807,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f292,f71])).

fof(f292,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f291,f60])).

fof(f291,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X2,sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f278,f61])).

fof(f278,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X2,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(superposition,[],[f95,f64])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f893,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f881,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f881,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f830,f101])).

fof(f830,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f829,f791])).

fof(f791,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK3) ),
    inference(forward_demodulation,[],[f790,f70])).

fof(f790,plain,(
    v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3) ),
    inference(subsumption_resolution,[],[f789,f238])).

fof(f238,plain,(
    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f217,f62])).

fof(f217,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f63,f78])).

fof(f789,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3) ),
    inference(forward_demodulation,[],[f784,f70])).

fof(f784,plain,
    ( ~ r2_hidden(k2_subset_1(u1_struct_0(sK3)),u1_pre_topc(sK3))
    | v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3) ),
    inference(resolution,[],[f227,f71])).

fof(f227,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X5,u1_pre_topc(sK3))
      | v3_pre_topc(X5,sK3) ) ),
    inference(resolution,[],[f63,f88])).

fof(f829,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f828,f70])).

fof(f828,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3) ),
    inference(forward_demodulation,[],[f821,f70])).

fof(f821,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3) ),
    inference(resolution,[],[f298,f71])).

fof(f298,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f297,f60])).

fof(f297,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(X5,sK3)
      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f281,f61])).

fof(f281,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(X5,sK3)
      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(superposition,[],[f97,f64])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1310,plain,(
    ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f1309,f1083])).

fof(f1083,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK1) ),
    inference(subsumption_resolution,[],[f1082,f58])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f1082,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1081,f59])).

fof(f1081,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1080,f416])).

fof(f1080,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1079,f392])).

fof(f1079,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f1042,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f1042,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f1041,f392])).

fof(f1041,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f1035])).

fof(f1035,plain,
    ( v1_tsep_1(sK2,sK1)
    | v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1) ),
    inference(resolution,[],[f972,f588])).

fof(f588,plain,(
    ! [X7] :
      ( ~ v3_pre_topc(u1_struct_0(X7),sK1)
      | v1_tsep_1(X7,sK1)
      | ~ m1_pre_topc(X7,sK1) ) ),
    inference(subsumption_resolution,[],[f123,f59])).

fof(f123,plain,(
    ! [X7] :
      ( v1_tsep_1(X7,sK1)
      | ~ v3_pre_topc(u1_struct_0(X7),sK1)
      | ~ m1_pre_topc(X7,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f85])).

fof(f120,plain,(
    ! [X7] :
      ( v1_tsep_1(X7,sK1)
      | ~ v3_pre_topc(u1_struct_0(X7),sK1)
      | ~ m1_subset_1(u1_struct_0(X7),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X7,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f58,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f972,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | v1_tsep_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f971,f416])).

fof(f971,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK2),sK1)
    | v1_tsep_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f918,f895])).

fof(f918,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tsep_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f897,f895])).

fof(f897,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | v1_tsep_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f251,f401])).

fof(f401,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f394,f59])).

fof(f394,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f392,f276])).

fof(f276,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f86,f64])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f251,plain,
    ( v1_tsep_1(sK2,sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f250,f58])).

fof(f250,plain,
    ( v1_tsep_1(sK2,sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f249,f59])).

fof(f249,plain,
    ( v1_tsep_1(sK2,sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f65,f110])).

fof(f65,plain,
    ( v1_tsep_1(sK3,sK1)
    | v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f1309,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f1308,f895])).

fof(f1308,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f1307,f1042])).

fof(f1307,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f1306,f392])).

fof(f1306,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f330,f401])).

fof(f330,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f329,f58])).

fof(f329,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f328,f59])).

fof(f328,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f69,f106])).

fof(f69,plain,
    ( ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:45:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.47  % (1055)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.48  % (1049)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (1032)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (1025)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (1021)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (1032)Refutation not found, incomplete strategy% (1032)------------------------------
% 0.20/0.48  % (1032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1042)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (1036)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.49  % (1019)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (1019)Refutation not found, incomplete strategy% (1019)------------------------------
% 0.20/0.50  % (1019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1020)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (1054)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (1048)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (1050)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (1019)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1019)Memory used [KB]: 10618
% 0.20/0.50  % (1019)Time elapsed: 0.093 s
% 0.20/0.50  % (1019)------------------------------
% 0.20/0.50  % (1019)------------------------------
% 0.20/0.50  % (1036)Refutation not found, incomplete strategy% (1036)------------------------------
% 0.20/0.50  % (1036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1032)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1032)Memory used [KB]: 6396
% 0.20/0.50  % (1032)Time elapsed: 0.088 s
% 0.20/0.50  % (1032)------------------------------
% 0.20/0.50  % (1032)------------------------------
% 0.20/0.50  % (1058)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (1063)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (1020)Refutation not found, incomplete strategy% (1020)------------------------------
% 0.20/0.50  % (1020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1020)Memory used [KB]: 10746
% 0.20/0.50  % (1020)Time elapsed: 0.109 s
% 0.20/0.50  % (1020)------------------------------
% 0.20/0.50  % (1020)------------------------------
% 0.20/0.50  % (1059)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (1062)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (1036)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1036)Memory used [KB]: 1791
% 0.20/0.51  % (1036)Time elapsed: 0.108 s
% 0.20/0.51  % (1036)------------------------------
% 0.20/0.51  % (1036)------------------------------
% 0.20/0.51  % (1048)Refutation not found, incomplete strategy% (1048)------------------------------
% 0.20/0.51  % (1048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1048)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1048)Memory used [KB]: 10874
% 0.20/0.51  % (1048)Time elapsed: 0.117 s
% 0.20/0.51  % (1048)------------------------------
% 0.20/0.51  % (1048)------------------------------
% 0.20/0.51  % (1053)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (1051)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (1038)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (1061)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (1064)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (1055)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1312,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f1311,f416])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f399,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    l1_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    (((~m1_pre_topc(sK3,sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & ((m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1)) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK1) | ~v1_tsep_1(X2,sK1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1)) & ((m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1)) | (m1_pre_topc(X1,sK1) & v1_tsep_1(X1,sK1))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK1) | ~v1_tsep_1(X2,sK1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1)) & ((m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1)) | (m1_pre_topc(X1,sK1) & v1_tsep_1(X1,sK1))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK1) | ~v1_tsep_1(X2,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & ((m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1)) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ? [X2] : ((~m1_pre_topc(X2,sK1) | ~v1_tsep_1(X2,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & ((m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1)) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK3,sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & ((m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1)) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).
% 0.20/0.52  fof(f399,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f392,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.52  fof(f392,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f387,f59])).
% 0.20/0.52  fof(f387,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f386])).
% 0.20/0.52  fof(f386,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | m1_pre_topc(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f316,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK1) | m1_pre_topc(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f316,plain,(
% 0.20/0.52    ( ! [X10] : (~m1_pre_topc(sK3,X10) | m1_pre_topc(sK2,X10) | ~l1_pre_topc(X10)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f315,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    v2_pre_topc(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    ( ! [X10] : (m1_pre_topc(sK2,X10) | ~m1_pre_topc(sK3,X10) | ~v2_pre_topc(sK3) | ~l1_pre_topc(X10)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f314,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    v2_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f314,plain,(
% 0.20/0.52    ( ! [X10] : (m1_pre_topc(sK2,X10) | ~m1_pre_topc(sK3,X10) | ~v2_pre_topc(sK2) | ~v2_pre_topc(sK3) | ~l1_pre_topc(X10)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f313,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    l1_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f313,plain,(
% 0.20/0.52    ( ! [X10] : (m1_pre_topc(sK2,X10) | ~m1_pre_topc(sK3,X10) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~v2_pre_topc(sK3) | ~l1_pre_topc(X10)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f286,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    l1_pre_topc(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    ( ! [X10] : (~l1_pre_topc(sK3) | m1_pre_topc(sK2,X10) | ~m1_pre_topc(sK3,X10) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~v2_pre_topc(sK3) | ~l1_pre_topc(X10)) )),
% 0.20/0.52    inference(superposition,[],[f104,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.20/0.52  fof(f1311,plain,(
% 0.20/0.52    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(forward_demodulation,[],[f1310,f895])).
% 0.20/0.52  fof(f895,plain,(
% 0.20/0.52    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f893,f844])).
% 0.20/0.52  fof(f844,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f817,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f817,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f816,f726])).
% 0.20/0.52  fof(f726,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f725,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f725,plain,(
% 0.20/0.52    v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f724,f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f171,f60])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~v2_pre_topc(sK2)),
% 0.20/0.52    inference(resolution,[],[f61,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(rectify,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(definition_folding,[],[f20,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.52    inference(rectify,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.20/0.52  fof(f724,plain,(
% 0.20/0.52    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f719,f70])).
% 0.20/0.52  fof(f719,plain,(
% 0.20/0.52    ~r2_hidden(k2_subset_1(u1_struct_0(sK2)),u1_pre_topc(sK2)) | v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2)),
% 0.20/0.52    inference(resolution,[],[f181,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X5,u1_pre_topc(sK2)) | v3_pre_topc(X5,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f61,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.52  fof(f816,plain,(
% 0.20/0.52    ~v3_pre_topc(u1_struct_0(sK2),sK2) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.52    inference(forward_demodulation,[],[f815,f70])).
% 0.20/0.52  fof(f815,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f807,f70])).
% 0.20/0.52  fof(f807,plain,(
% 0.20/0.52    m1_subset_1(k2_subset_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(k2_subset_1(u1_struct_0(sK2)),sK2)),
% 0.20/0.52    inference(resolution,[],[f292,f71])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X2,sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f291,f60])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X2,sK2) | ~v2_pre_topc(sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f278,f61])).
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.20/0.52    inference(superposition,[],[f95,f64])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.20/0.52  fof(f893,plain,(
% 0.20/0.52    u1_struct_0(sK2) = u1_struct_0(sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f881,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f881,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f830,f101])).
% 0.20/0.52  fof(f830,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f829,f791])).
% 0.20/0.52  fof(f791,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK3),sK3)),
% 0.20/0.52    inference(forward_demodulation,[],[f790,f70])).
% 0.20/0.52  fof(f790,plain,(
% 0.20/0.52    v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f789,f238])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f217,f62])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~v2_pre_topc(sK3)),
% 0.20/0.52    inference(resolution,[],[f63,f78])).
% 0.20/0.52  fof(f789,plain,(
% 0.20/0.52    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3)),
% 0.20/0.52    inference(forward_demodulation,[],[f784,f70])).
% 0.20/0.52  fof(f784,plain,(
% 0.20/0.52    ~r2_hidden(k2_subset_1(u1_struct_0(sK3)),u1_pre_topc(sK3)) | v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3)),
% 0.20/0.52    inference(resolution,[],[f227,f71])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(X5,u1_pre_topc(sK3)) | v3_pre_topc(X5,sK3)) )),
% 0.20/0.52    inference(resolution,[],[f63,f88])).
% 0.20/0.52  fof(f829,plain,(
% 0.20/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK3) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(forward_demodulation,[],[f828,f70])).
% 0.20/0.52  fof(f828,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3)),
% 0.20/0.52    inference(forward_demodulation,[],[f821,f70])).
% 0.20/0.52  fof(f821,plain,(
% 0.20/0.52    m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(k2_subset_1(u1_struct_0(sK3)),sK3)),
% 0.20/0.52    inference(resolution,[],[f298,f71])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X5,sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f297,f60])).
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    ( ! [X5] : (~v3_pre_topc(X5,sK3) | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f281,f61])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X5] : (~v3_pre_topc(X5,sK3) | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.20/0.52    inference(superposition,[],[f97,f64])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f54])).
% 0.20/0.52  fof(f1310,plain,(
% 0.20/0.52    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1309,f1083])).
% 0.20/0.52  fof(f1083,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1082,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    v2_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f1082,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1081,f59])).
% 0.20/0.52  fof(f1081,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1080,f416])).
% 0.20/0.52  fof(f1080,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1079,f392])).
% 0.20/0.52  fof(f1079,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f1042,f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.52  fof(f1042,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1041,f392])).
% 0.20/0.52  fof(f1041,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f1035])).
% 0.20/0.52  fof(f1035,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1) | v1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f972,f588])).
% 0.20/0.52  fof(f588,plain,(
% 0.20/0.52    ( ! [X7] : (~v3_pre_topc(u1_struct_0(X7),sK1) | v1_tsep_1(X7,sK1) | ~m1_pre_topc(X7,sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f123,f59])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X7] : (v1_tsep_1(X7,sK1) | ~v3_pre_topc(u1_struct_0(X7),sK1) | ~m1_pre_topc(X7,sK1) | ~l1_pre_topc(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f120,f85])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X7] : (v1_tsep_1(X7,sK1) | ~v3_pre_topc(u1_struct_0(X7),sK1) | ~m1_subset_1(u1_struct_0(X7),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X7,sK1) | ~l1_pre_topc(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f58,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f972,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1) | v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f971,f416])).
% 0.20/0.52  fof(f971,plain,(
% 0.20/0.52    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK2),sK1) | v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f918,f895])).
% 0.20/0.52  fof(f918,plain,(
% 0.20/0.52    v3_pre_topc(u1_struct_0(sK2),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f897,f895])).
% 0.20/0.52  fof(f897,plain,(
% 0.20/0.52    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f251,f401])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f394,f59])).
% 0.20/0.52  fof(f394,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f392,f276])).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(superposition,[],[f86,f64])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f250,f58])).
% 0.20/0.52  fof(f250,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f249,f59])).
% 0.20/0.52  fof(f249,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f65,f110])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    v1_tsep_1(sK3,sK1) | v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f1309,plain,(
% 0.20/0.52    ~v3_pre_topc(u1_struct_0(sK2),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(forward_demodulation,[],[f1308,f895])).
% 0.20/0.52  fof(f1308,plain,(
% 0.20/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1307,f1042])).
% 0.20/0.52  fof(f1307,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1306,f392])).
% 0.20/0.52  fof(f1306,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f330,f401])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f329,f58])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f328,f59])).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f327])).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f69,f106])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (1055)------------------------------
% 0.20/0.52  % (1055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1055)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (1055)Memory used [KB]: 2046
% 0.20/0.52  % (1055)Time elapsed: 0.118 s
% 0.20/0.52  % (1055)------------------------------
% 0.20/0.52  % (1055)------------------------------
% 0.20/0.52  % (1017)Success in time 0.171 s
%------------------------------------------------------------------------------
