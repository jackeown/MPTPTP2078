%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1246+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:33 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  150 (2176 expanded)
%              Number of leaves         :   13 ( 714 expanded)
%              Depth                    :   33
%              Number of atoms          :  823 (29568 expanded)
%              Number of equality atoms :   22 ( 300 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2605,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2604,f1567])).

fof(f1567,plain,(
    ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(condensation,[],[f1559])).

fof(f1559,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f1549,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1549,plain,(
    ! [X0] : ~ r2_hidden(sK2,k3_xboole_0(k2_tops_1(sK0,sK1),X0)) ),
    inference(subsumption_resolution,[],[f1548,f1525])).

fof(f1525,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(X0,k3_xboole_0(k2_tops_1(sK0,sK1),X1)) ) ),
    inference(resolution,[],[f842,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f842,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_tops_1(sK0,sK1))
      | r2_hidden(X4,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(superposition,[],[f67,f417])).

fof(f417,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f415,f220])).

fof(f220,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f197,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
          | r1_xboole_0(sK1,sK3) )
        & r2_hidden(sK2,sK3)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) )
    & ( ! [X4] :
          ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X4)
            & ~ r1_xboole_0(sK1,X4) )
          | ~ r2_hidden(sK2,X4)
          | ~ v3_pre_topc(X4,sK0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                        | r1_xboole_0(X1,X3) )
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_tops_1(X0,X1)) )
                & ( ! [X4] :
                      ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X4)
                        & ~ r1_xboole_0(X1,X4) )
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,k2_tops_1(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),X3)
                      | r1_xboole_0(X1,X3) )
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X2,k2_tops_1(sK0,X1)) )
              & ( ! [X4] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),X4)
                      & ~ r1_xboole_0(X1,X4) )
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,sK0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | r2_hidden(X2,k2_tops_1(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),X3)
                    | r1_xboole_0(X1,X3) )
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X2,k2_tops_1(sK0,X1)) )
            & ( ! [X4] :
                  ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),X4)
                    & ~ r1_xboole_0(X1,X4) )
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,sK0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | r2_hidden(X2,k2_tops_1(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X3)
                  | r1_xboole_0(sK1,X3) )
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X2,k2_tops_1(sK0,sK1)) )
          & ( ! [X4] :
                ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X4)
                  & ~ r1_xboole_0(sK1,X4) )
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,sK0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X2,k2_tops_1(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X3)
                | r1_xboole_0(sK1,X3) )
              & r2_hidden(X2,X3)
              & v3_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X2,k2_tops_1(sK0,sK1)) )
        & ( ! [X4] :
              ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X4)
                & ~ r1_xboole_0(sK1,X4) )
              | ~ r2_hidden(X2,X4)
              | ~ v3_pre_topc(X4,sK0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X2,k2_tops_1(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ? [X3] :
            ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X3)
              | r1_xboole_0(sK1,X3) )
            & r2_hidden(sK2,X3)
            & v3_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) )
      & ( ! [X4] :
            ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X4)
              & ~ r1_xboole_0(sK1,X4) )
            | ~ r2_hidden(sK2,X4)
            | ~ v3_pre_topc(X4,sK0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK2,k2_tops_1(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X3)
          | r1_xboole_0(sK1,X3) )
        & r2_hidden(sK2,X3)
        & v3_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
        | r1_xboole_0(sK1,sK3) )
      & r2_hidden(sK2,sK3)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      | r1_xboole_0(X1,X3) )
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_tops_1(X0,X1)) )
              & ( ! [X4] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X4)
                      & ~ r1_xboole_0(X1,X4) )
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_tops_1(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      | r1_xboole_0(X1,X3) )
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_tops_1(X0,X1)) )
              & ( ! [X3] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      & ~ r1_xboole_0(X1,X3) )
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_tops_1(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      | r1_xboole_0(X1,X3) )
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_tops_1(X0,X1)) )
              & ( ! [X3] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      & ~ r1_xboole_0(X1,X3) )
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_tops_1(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_tops_1(X0,X1))
              <~> ! [X3] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      & ~ r1_xboole_0(X1,X3) )
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_tops_1(X0,X1))
              <~> ! [X3] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      & ~ r1_xboole_0(X1,X3) )
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_tops_1(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) )
                       => ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                          & ~ r1_xboole_0(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_tops_1(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) )
                     => ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                        & ~ r1_xboole_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tops_1)).

fof(f197,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f126,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f126,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f415,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f127,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f127,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1548,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k3_xboole_0(k2_tops_1(sK0,sK1),X0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f1547,f68])).

fof(f1547,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k3_xboole_0(k2_tops_1(sK0,sK1),X0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1541,f126])).

fof(f1541,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k3_xboole_0(k2_tops_1(sK0,sK1),X0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f918,f528])).

fof(f528,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f527,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f527,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f526,f46])).

fof(f46,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f526,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f525,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f525,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f524,f40])).

fof(f524,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f523,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f523,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f187,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f187,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ r1_xboole_0(X2,sK3)
      | ~ v3_pre_topc(sK3,X3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r2_hidden(sK2,k2_pre_topc(X3,X2))
      | ~ m1_subset_1(sK2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK4(X0,X1,X2))
                    & r2_hidden(X2,sK4(X0,X1,X2))
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

fof(f47,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f918,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
      | ~ r2_hidden(sK2,k3_xboole_0(k2_tops_1(sK0,sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f916,f852])).

fof(f852,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X0,k3_xboole_0(k2_tops_1(sK0,sK1),X1)) ) ),
    inference(resolution,[],[f843,f68])).

fof(f843,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_tops_1(sK0,sK1))
      | r2_hidden(X5,k2_pre_topc(sK0,sK1)) ) ),
    inference(superposition,[],[f68,f417])).

fof(f916,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK2,k3_xboole_0(k2_tops_1(sK0,sK1),X0)) ) ),
    inference(resolution,[],[f508,f68])).

fof(f508,plain,
    ( ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f507,f45])).

fof(f507,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f506,f46])).

fof(f506,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f505,f47])).

fof(f505,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f503,f41])).

fof(f503,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,
    ( r1_xboole_0(sK1,sK3)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f39])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f42,f50])).

fof(f2604,plain,(
    r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2603,f417])).

fof(f2603,plain,(
    r2_hidden(sK2,k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(subsumption_resolution,[],[f2595,f1567])).

fof(f2595,plain,
    ( r2_hidden(sK2,k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f2577,f928])).

fof(f928,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2,X1)
      | r2_hidden(sK2,k3_xboole_0(k2_pre_topc(sK0,sK1),X1))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f925,f621])).

fof(f621,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k3_xboole_0(k2_pre_topc(sK0,sK1),X1))
      | ~ r2_hidden(sK2,X1) ) ),
    inference(resolution,[],[f418,f66])).

fof(f418,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f136,f42])).

fof(f136,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f135,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f39])).

fof(f134,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f925,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | r2_hidden(sK2,k3_xboole_0(k2_pre_topc(sK0,sK1),X1))
      | ~ r2_hidden(sK2,X1) ) ),
    inference(resolution,[],[f412,f66])).

fof(f412,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f411,f359])).

fof(f359,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f139,f42])).

fof(f139,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | r2_hidden(X5,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f138,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f411,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f410,f360])).

fof(f360,plain,
    ( r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f142,f42])).

fof(f142,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | r2_hidden(X6,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f141,f38])).

fof(f141,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,sK1))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f140,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,sK1))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f40])).

fof(f121,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,sK1))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f410,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f409,f41])).

fof(f409,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(sK1,X4)
      | ~ r2_hidden(sK2,X4)
      | ~ v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,(
    ! [X5] :
      ( r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f114,plain,(
    ! [X5] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f113,plain,(
    ! [X5] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f40])).

fof(f100,plain,(
    ! [X5] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2577,plain,(
    r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f2576,f1039])).

fof(f1039,plain,
    ( m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f210,f42])).

fof(f210,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f209,f38])).

fof(f209,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f208,f39])).

fof(f208,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f40])).

fof(f193,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f126,f51])).

fof(f2576,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2575,f1117])).

fof(f1117,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f219,f42])).

fof(f219,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X7))
      | r2_hidden(X7,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f218,f38])).

fof(f218,plain,(
    ! [X7] :
      ( r2_hidden(X7,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X7))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f39])).

fof(f217,plain,(
    ! [X7] :
      ( r2_hidden(X7,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X7))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f40])).

fof(f196,plain,(
    ! [X7] :
      ( r2_hidden(X7,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X7))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f126,f54])).

fof(f2575,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | ~ m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2574,f972])).

fof(f972,plain,
    ( r2_hidden(sK2,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f216,f42])).

fof(f216,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X6))
      | r2_hidden(X6,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f215,f38])).

fof(f215,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r2_hidden(X6,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f214,f39])).

fof(f214,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r2_hidden(X6,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f40])).

fof(f195,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r2_hidden(X6,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f126,f53])).

fof(f2574,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | ~ m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2569,f1567])).

fof(f2569,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | ~ m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f971,f44])).

fof(f44,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK2,X4)
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f971,plain,
    ( v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f213,f42])).

fof(f213,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X5),sK0)
      | r2_hidden(X5,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f212,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f211,f39])).

fof(f211,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f40])).

fof(f194,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f126,f52])).

%------------------------------------------------------------------------------
