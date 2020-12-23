%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2047+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:05 EST 2020

% Result     : Theorem 11.52s
% Output     : Refutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  192 (1096 expanded)
%              Number of leaves         :   27 ( 361 expanded)
%              Depth                    :   45
%              Number of atoms          : 1036 (17164 expanded)
%              Number of equality atoms :   46 (  96 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6307,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6225,f794])).

fof(f794,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f793,f93])).

fof(f93,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_waybel_7(sK0,sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(sK3)
        & r2_hidden(sK2,sK1)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(sK1,X5)
              | ~ r2_waybel_7(sK0,X5,X4)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
              | v1_xboole_0(X5) )
          | ~ r2_hidden(X4,sK1)
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f60,f59,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X1,X3)
                      & r2_waybel_7(X0,X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X1,X5)
                      | ~ r2_waybel_7(X0,X5,X4)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X5) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(sK0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v3_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(sK0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r2_waybel_7(sK0,X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                  & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                  & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                  & ~ v1_xboole_0(X3) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ v3_pre_topc(X1,sK0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X1,X5)
                  | ~ r2_waybel_7(sK0,X5,X4)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                  | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                  | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                  | v1_xboole_0(X5) )
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(sK1,X3)
                & r2_waybel_7(sK0,X3,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                & ~ v1_xboole_0(X3) )
            & r2_hidden(X2,sK1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ v3_pre_topc(sK1,sK0) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(sK1,X5)
                | ~ r2_waybel_7(sK0,X5,X4)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                | v1_xboole_0(X5) )
            | ~ r2_hidden(X4,sK1)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(sK1,X3)
            & r2_waybel_7(sK0,X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
            & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
            & ~ v1_xboole_0(X3) )
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_hidden(sK1,X3)
          & r2_waybel_7(sK0,X3,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
          & ~ v1_xboole_0(X3) )
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_waybel_7(sK0,X3,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(X3) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_waybel_7(sK0,sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(X0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ( r2_waybel_7(X0,X3,X2)
                         => r2_hidden(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                        & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                        & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ( r2_waybel_7(X0,X3,X2)
                       => r2_hidden(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow19)).

fof(f793,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,sK3) ),
    inference(subsumption_resolution,[],[f792,f87])).

fof(f87,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f792,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f786])).

fof(f786,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,sK3)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f253,f92])).

fof(f92,plain,
    ( r2_waybel_7(sK0,sK3,sK2)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ r2_waybel_7(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | ~ v3_pre_topc(sK1,sK0)
      | r2_hidden(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f252,f82])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f252,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ v3_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,X0,X1)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f238,f83])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ v3_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,X0,X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f84,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).

fof(f67,plain,(
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

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f6225,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f248,f6077])).

fof(f6077,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f6032])).

fof(f6032,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f1176,f5991])).

fof(f5991,plain,(
    o_0_0_xboole_0 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f5824,f753])).

fof(f753,plain,(
    ! [X8] :
      ( r2_hidden(sK5(X8,o_0_0_xboole_0),X8)
      | o_0_0_xboole_0 = X8 ) ),
    inference(resolution,[],[f716,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f69,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f716,plain,(
    ! [X4] : ~ r2_hidden(X4,o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f712,f418])).

fof(f418,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,o_0_0_xboole_0)
      | r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f144,f261])).

fof(f261,plain,(
    o_0_0_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f245,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f126,f95])).

fof(f95,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f245,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f144,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
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
    inference(rectify,[],[f77])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f712,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,o_0_0_xboole_0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f143,f329])).

fof(f329,plain,(
    o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f260,f138])).

fof(f260,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f241,f83])).

fof(f241,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f84,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f143,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f5824,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f5814,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f5814,plain,(
    v1_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f5803,f1700])).

fof(f1700,plain,
    ( v1_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | r2_hidden(o_2_3_yellow19(sK0,sK1),sK1) ),
    inference(resolution,[],[f571,f144])).

fof(f571,plain,
    ( r2_hidden(o_2_3_yellow19(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v1_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f570,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f570,plain,(
    m1_subset_1(o_2_3_yellow19(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f251,f243])).

fof(f243,plain,(
    ! [X5] : k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5) ),
    inference(resolution,[],[f84,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f251,plain,(
    m1_subset_1(o_2_3_yellow19(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f250,f81])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f250,plain,
    ( m1_subset_1(o_2_3_yellow19(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f82])).

fof(f249,plain,
    ( m1_subset_1(o_2_3_yellow19(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f237,f83])).

fof(f237,plain,
    ( m1_subset_1(o_2_3_yellow19(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f84,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_3_yellow19)).

fof(f5803,plain,
    ( v1_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ r2_hidden(o_2_3_yellow19(sK0,sK1),sK1) ),
    inference(resolution,[],[f1701,f3693])).

fof(f3693,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X6,sK1) ) ),
    inference(subsumption_resolution,[],[f3692,f242])).

fof(f242,plain,(
    ! [X4] :
      ( m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f84,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3692,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | r2_hidden(X6,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3691,f81])).

fof(f3691,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | r2_hidden(X6,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3690,f82])).

fof(f3690,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | r2_hidden(X6,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3689,f83])).

fof(f3689,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | r2_hidden(X6,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3684,f84])).

fof(f3684,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | r2_hidden(X6,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3658,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f3658,plain,(
    ! [X0] :
      ( m1_connsp_2(sK1,sK0,X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f3649])).

fof(f3649,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f2883,f390])).

fof(f390,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X8,sK1) ) ),
    inference(subsumption_resolution,[],[f389,f81])).

fof(f389,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK1)
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f388,f82])).

fof(f388,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK1)
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f368,f83])).

fof(f368,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK1)
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f242,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f2883,plain,(
    ! [X4] :
      ( r2_hidden(sK1,k1_yellow19(sK0,X4))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f2880,f242])).

fof(f2880,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(sK1,k1_yellow19(sK0,X4)) ) ),
    inference(duplicate_literal_removal,[],[f2874])).

fof(f2874,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(sK1,k1_yellow19(sK0,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1071,f141])).

fof(f141,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
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

fof(f1071,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(k1_yellow19(sK0,X9),k1_yellow19(sK0,X8))
      | ~ r2_hidden(X9,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | r2_hidden(sK1,k1_yellow19(sK0,X8))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1070,f232])).

fof(f232,plain,(
    ! [X28] :
      ( v13_waybel_0(k1_yellow19(sK0,X28),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X28,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f231,f81])).

fof(f231,plain,(
    ! [X28] :
      ( v13_waybel_0(k1_yellow19(sK0,X28),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X28,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f203,f82])).

fof(f203,plain,(
    ! [X28] :
      ( v13_waybel_0(k1_yellow19(sK0,X28),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X28,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow19)).

fof(f1070,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1,k1_yellow19(sK0,X8))
      | ~ r2_hidden(X9,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_tarski(k1_yellow19(sK0,X9),k1_yellow19(sK0,X8))
      | ~ v13_waybel_0(k1_yellow19(sK0,X8),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1069,f224])).

fof(f224,plain,(
    ! [X24] :
      ( m1_subset_1(k1_yellow19(sK0,X24),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ m1_subset_1(X24,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f223,f81])).

fof(f223,plain,(
    ! [X24] :
      ( m1_subset_1(k1_yellow19(sK0,X24),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f82])).

fof(f199,plain,(
    ! [X24] :
      ( m1_subset_1(k1_yellow19(sK0,X24),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow19)).

fof(f1069,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1,k1_yellow19(sK0,X8))
      | ~ r2_hidden(X9,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_tarski(k1_yellow19(sK0,X9),k1_yellow19(sK0,X8))
      | ~ m1_subset_1(k1_yellow19(sK0,X8),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(k1_yellow19(sK0,X8),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1068,f81])).

fof(f1068,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1,k1_yellow19(sK0,X8))
      | ~ r2_hidden(X9,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_tarski(k1_yellow19(sK0,X9),k1_yellow19(sK0,X8))
      | ~ m1_subset_1(k1_yellow19(sK0,X8),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(k1_yellow19(sK0,X8),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1067,f82])).

fof(f1067,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1,k1_yellow19(sK0,X8))
      | ~ r2_hidden(X9,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_tarski(k1_yellow19(sK0,X9),k1_yellow19(sK0,X8))
      | ~ m1_subset_1(k1_yellow19(sK0,X8),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(k1_yellow19(sK0,X8),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1058,f83])).

fof(f1058,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1,k1_yellow19(sK0,X8))
      | ~ r2_hidden(X9,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_tarski(k1_yellow19(sK0,X9),k1_yellow19(sK0,X8))
      | ~ m1_subset_1(k1_yellow19(sK0,X8),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(k1_yellow19(sK0,X8),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1053,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X2,X1)
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f1053,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1052,f242])).

fof(f1052,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1051,f226])).

fof(f226,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(k1_yellow19(sK0,X25))
      | ~ m1_subset_1(X25,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f225,f81])).

fof(f225,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(k1_yellow19(sK0,X25))
      | ~ m1_subset_1(X25,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f82])).

fof(f200,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(k1_yellow19(sK0,X25))
      | ~ m1_subset_1(X25,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1051,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1050,f230])).

fof(f230,plain,(
    ! [X27] :
      ( v2_waybel_0(k1_yellow19(sK0,X27),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X27,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f229,f81])).

fof(f229,plain,(
    ! [X27] :
      ( v2_waybel_0(k1_yellow19(sK0,X27),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f202,f82])).

fof(f202,plain,(
    ! [X27] :
      ( v2_waybel_0(k1_yellow19(sK0,X27),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1050,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ v2_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1049,f232])).

fof(f1049,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ v13_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f363,f794])).

fof(f363,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ v13_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f362,f81])).

fof(f362,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ v13_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f361,f82])).

fof(f361,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ v13_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f357,f83])).

fof(f357,plain,(
    ! [X8,X7] :
      ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X7),X8)
      | r2_hidden(sK1,k1_yellow19(sK0,X7))
      | ~ v13_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(k1_yellow19(sK0,X7),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k1_yellow19(sK0,X7))
      | ~ r2_hidden(X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f85,f111])).

fof(f85,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ r2_waybel_7(sK0,X5,X4)
      | r2_hidden(sK1,X5)
      | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1701,plain,
    ( ~ r2_hidden(o_2_3_yellow19(sK0,sK1),k1_tops_1(sK0,sK1))
    | v1_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f571,f143])).

fof(f1176,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f331,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f125,f95])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f331,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f260,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f248,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f247,f82])).

fof(f247,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f236,f83])).

fof(f236,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f84,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

%------------------------------------------------------------------------------
