%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t61_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:30 EDT 2019

% Result     : Theorem 4.52s
% Output     : Refutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  147 (1497 expanded)
%              Number of leaves         :   14 ( 501 expanded)
%              Depth                    :   24
%              Number of atoms          :  821 (21002 expanded)
%              Number of equality atoms :   22 (  80 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26529,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26528,f21702])).

fof(f21702,plain,(
    ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21700,f5417])).

fof(f5417,plain,(
    r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f5416,f3151])).

fof(f3151,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_tops_1(sK0,sK1))
      | r2_hidden(X4,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(superposition,[],[f150,f836])).

fof(f836,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f833,f491])).

fof(f491,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f457,f98])).

fof(f98,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f74,f78,f77,f76,f75])).

fof(f75,plain,
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

fof(f76,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),sK1),X3)
                    | r1_xboole_0(sK1,X3) )
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k2_tops_1(X0,sK1)) )
            & ( ! [X4] :
                  ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),sK1),X4)
                    & ~ r1_xboole_0(sK1,X4) )
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,k2_tops_1(X0,sK1)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
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
     => ( ( ? [X3] :
              ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                | r1_xboole_0(X1,X3) )
              & r2_hidden(sK2,X3)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK2,k2_tops_1(X0,X1)) )
        & ( ! [X4] :
              ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X4)
                & ~ r1_xboole_0(X1,X4) )
              | ~ r2_hidden(sK2,X4)
              | ~ v3_pre_topc(X4,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK2,k2_tops_1(X0,X1)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
            | r1_xboole_0(X1,X3) )
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),sK3)
          | r1_xboole_0(X1,sK3) )
        & r2_hidden(X2,sK3)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
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
    inference(rectify,[],[f73])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',t61_tops_1)).

fof(f457,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f211,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',dt_k2_pre_topc)).

fof(f211,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f99,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',dt_k3_subset_1)).

fof(f99,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

fof(f833,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f221,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',redefinition_k9_subset_1)).

fof(f221,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f201,f98])).

fof(f201,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f99,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',d2_tops_1)).

fof(f150,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
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
    inference(rectify,[],[f88])).

fof(f88,plain,(
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
    inference(flattening,[],[f87])).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',d4_xboole_0)).

fof(f5416,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5415,f211])).

fof(f5415,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f5409])).

fof(f5409,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f765,f200])).

fof(f200,plain,(
    ! [X5] :
      ( r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f199,f96])).

fof(f96,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f199,plain,(
    ! [X5] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f97])).

fof(f97,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f198,plain,(
    ! [X5] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f98])).

fof(f187,plain,(
    ! [X5] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X5))
      | r1_xboole_0(X5,sK4(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f81,f82])).

fof(f82,plain,(
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

fof(f81,plain,(
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
    inference(rectify,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',t39_tops_1)).

fof(f100,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f79])).

fof(f765,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,X0,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f764,f191])).

fof(f191,plain,(
    ! [X2] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X2))
      | m1_subset_1(sK4(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f190,f96])).

fof(f190,plain,(
    ! [X2] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X2))
      | m1_subset_1(sK4(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f189,f97])).

fof(f189,plain,(
    ! [X2] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X2))
      | m1_subset_1(sK4(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f98])).

fof(f184,plain,(
    ! [X2] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X2))
      | m1_subset_1(sK4(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f764,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,X0,sK2))
      | ~ m1_subset_1(sK4(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f761,f197])).

fof(f197,plain,(
    ! [X4] :
      ( r2_hidden(sK2,sK4(sK0,X4,sK2))
      | r2_hidden(sK2,k2_pre_topc(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f196,f96])).

fof(f196,plain,(
    ! [X4] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X4))
      | r2_hidden(sK2,sK4(sK0,X4,sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f97])).

fof(f195,plain,(
    ! [X4] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X4))
      | r2_hidden(sK2,sK4(sK0,X4,sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f98])).

fof(f186,plain,(
    ! [X4] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X4))
      | r2_hidden(sK2,sK4(sK0,X4,sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f761,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,sK4(sK0,X0,sK2))
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK4(sK0,X0,sK2))
      | ~ m1_subset_1(sK4(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f194,f102])).

fof(f102,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK2,X4)
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f194,plain,(
    ! [X3] :
      ( v3_pre_topc(sK4(sK0,X3,sK2),sK0)
      | r2_hidden(sK2,k2_pre_topc(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f193,f96])).

fof(f193,plain,(
    ! [X3] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X3))
      | v3_pre_topc(sK4(sK0,X3,sK2),sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f97])).

fof(f192,plain,(
    ! [X3] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X3))
      | v3_pre_topc(sK4(sK0,X3,sK2),sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f98])).

fof(f185,plain,(
    ! [X3] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X3))
      | v3_pre_topc(sK4(sK0,X3,sK2),sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f21700,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f21694])).

fof(f21694,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f5533,f105])).

fof(f105,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f5533,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,sK3)
      | ~ r2_hidden(X13,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f5532,f4265])).

fof(f4265,plain,
    ( ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3) ),
    inference(subsumption_resolution,[],[f4264,f3152])).

fof(f3152,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_tops_1(sK0,sK1))
      | r2_hidden(X5,k2_pre_topc(sK0,sK1)) ) ),
    inference(superposition,[],[f151,f836])).

fof(f151,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f4264,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3) ),
    inference(subsumption_resolution,[],[f4263,f99])).

fof(f4263,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3) ),
    inference(duplicate_literal_removal,[],[f4261])).

fof(f4261,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1020,f106])).

fof(f106,plain,
    ( r1_xboole_0(sK1,sK3)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f1020,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1019,f103])).

fof(f103,plain,
    ( ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

fof(f1019,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1018,f104])).

fof(f104,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f1018,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1017,f96])).

fof(f1017,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1016,f98])).

fof(f1016,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1015,f100])).

fof(f1015,plain,(
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
    inference(resolution,[],[f252,f97])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ r1_xboole_0(X0,sK3)
      | ~ v3_pre_topc(sK3,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2,k2_pre_topc(X1,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f105,f114])).

fof(f114,plain,(
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
    inference(cnf_transformation,[],[f83])).

fof(f5532,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,sK3)
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
      | ~ r2_hidden(X13,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f5526,f103])).

fof(f5526,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,sK3)
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X13,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f474,f104])).

fof(f474,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f473,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t61_tops_1.p',t4_subset)).

fof(f473,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
      | ~ r2_hidden(X1,X0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f472,f96])).

fof(f472,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
      | ~ r2_hidden(X1,X0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f471,f97])).

fof(f471,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
      | ~ r2_hidden(X1,X0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f450,f98])).

fof(f450,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
      | ~ r2_hidden(X1,X0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f211,f114])).

fof(f26528,plain,(
    r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f26503,f5417])).

fof(f26503,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f26491])).

fof(f26491,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f3150,f2376])).

fof(f2376,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2375,f839])).

fof(f839,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f231,f100])).

fof(f231,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f230,f96])).

fof(f230,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f97])).

fof(f229,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f204,f98])).

fof(f204,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | m1_subset_1(sK4(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f99,f115])).

fof(f2375,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2374,f759])).

fof(f759,plain,
    ( r1_xboole_0(sK1,sK4(sK0,sK1,sK2))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f240,f100])).

fof(f240,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r1_xboole_0(sK1,sK4(sK0,sK1,X7))
      | r2_hidden(X7,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f239,f96])).

fof(f239,plain,(
    ! [X7] :
      ( r2_hidden(X7,k2_pre_topc(sK0,sK1))
      | r1_xboole_0(sK1,sK4(sK0,sK1,X7))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f238,f97])).

fof(f238,plain,(
    ! [X7] :
      ( r2_hidden(X7,k2_pre_topc(sK0,sK1))
      | r1_xboole_0(sK1,sK4(sK0,sK1,X7))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f207,f98])).

fof(f207,plain,(
    ! [X7] :
      ( r2_hidden(X7,k2_pre_topc(sK0,sK1))
      | r1_xboole_0(sK1,sK4(sK0,sK1,X7))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f99,f118])).

fof(f2374,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r1_xboole_0(sK1,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2368,f754])).

fof(f754,plain,
    ( r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f237,f100])).

fof(f237,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | r2_hidden(X6,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f236,f96])).

fof(f236,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,sK1))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f97])).

fof(f235,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,sK1))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f206,f98])).

fof(f206,plain,(
    ! [X6] :
      ( r2_hidden(X6,k2_pre_topc(sK0,sK1))
      | r2_hidden(X6,sK4(sK0,sK1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f99,f117])).

fof(f2368,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | ~ r1_xboole_0(sK1,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f750,f101])).

fof(f101,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK2,X4)
      | ~ r1_xboole_0(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f750,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f234,f100])).

fof(f234,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | r2_hidden(X5,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f233,f96])).

fof(f233,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f97])).

fof(f232,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f98])).

fof(f205,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | v3_pre_topc(sK4(sK0,sK1,X5),sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f99,f116])).

fof(f3150,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X3,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | r2_hidden(X3,k2_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f149,f836])).

fof(f149,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).
%------------------------------------------------------------------------------
