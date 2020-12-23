%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  285 (43591 expanded)
%              Number of leaves         :   19 (15538 expanded)
%              Depth                    :   88
%              Number of atoms          : 1456 (463089 expanded)
%              Number of equality atoms :  466 (56734 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f801,plain,(
    $false ),
    inference(subsumption_resolution,[],[f800,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    & ! [X3] :
        ( k1_funct_1(sK2,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(X1))
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(sK1))
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2)
        & ! [X3] :
            ( k1_funct_1(X2,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(sK1))
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
      & ! [X3] :
          ( k1_funct_1(sK2,X3) = X3
          | ~ r2_hidden(X3,u1_struct_0(sK1))
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f800,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f799,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f799,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f798,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f798,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f794,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f794,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f765])).

fof(f765,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f677,f441])).

fof(f441,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f439,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f439,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(resolution,[],[f437,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f437,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,sK2,sK2) ) ),
    inference(resolution,[],[f436,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f436,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
                & m1_subset_1(sK4(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
        & m1_subset_1(sK4(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

fof(f677,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f61,f676])).

fof(f676,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f675,f52])).

fof(f675,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f674,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f674,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f673,f54])).

fof(f673,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f672,f56])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f672,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f671,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f671,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f670,f216])).

fof(f216,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f52])).

fof(f215,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f53])).

fof(f214,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f213,f54])).

fof(f213,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f56])).

fof(f212,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f211,f72])).

fof(f211,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f113])).

fof(f113,plain,(
    v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f111,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f111,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f109,f52])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f74,f53])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f210,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f209,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f209,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f208,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f207,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f206,f54])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f56])).

fof(f205,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f174,f72])).

fof(f174,plain,(
    ! [X2] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f113])).

fof(f168,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f67,f163])).

fof(f163,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f126,f160])).

fof(f160,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f125])).

fof(f125,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f111,f117])).

fof(f117,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f116,f100])).

fof(f100,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f116,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f59])).

fof(f114,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f80,f58])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f159,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f157,f80])).

fof(f157,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f52])).

fof(f156,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f54])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f154,f56])).

fof(f154,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(X3)
      | ~ m1_pre_topc(sK1,X3)
      | ~ l1_pre_topc(X3)
      | v1_funct_2(k4_tmap_1(X3,sK1),k1_relat_1(sK2),u1_struct_0(X3))
      | v2_struct_0(X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f73,f117])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f126,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f112,f117])).

fof(f112,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f111,f79])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(f670,plain,
    ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f669,f656])).

fof(f656,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f639])).

fof(f639,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f638,f401])).

fof(f401,plain,
    ( ~ r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f393,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f393,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f390,f384])).

fof(f384,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f383,f222])).

fof(f222,plain,
    ( r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f216,f182])).

fof(f182,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f180,f112])).

fof(f180,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f111])).

fof(f179,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f171,f80])).

fof(f171,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f117])).

fof(f170,plain,
    ( u1_struct_0(sK1) != k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( u1_struct_0(sK1) != k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f145,f163])).

fof(f145,plain,
    ( u1_struct_0(sK1) != k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f141,f112])).

fof(f141,plain,
    ( u1_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f82,f111])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f383,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f381,f97])).

fof(f97,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f59])).

fof(f381,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ v1_relat_1(sK2)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f357,f57])).

fof(f357,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),u1_struct_0(sK1))
      | ~ v1_relat_1(X0)
      | r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ r1_tarski(u1_struct_0(sK1),k1_relat_1(X0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f356,f182])).

fof(f356,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f355,f52])).

fof(f355,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f354,f53])).

fof(f354,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f353,f54])).

fof(f353,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f352,f56])).

fof(f352,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1)))
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f201,f113])).

fof(f201,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(k4_tmap_1(X1,X2))
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(X1,X2)),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k4_tmap_1(X1,X2),X3)
      | r2_hidden(sK3(k4_tmap_1(X1,X2),X3),k1_relat_1(k4_tmap_1(X1,X2)))
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f69,f72])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f390,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f366,f107])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f105,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f104,f56])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f66,f54])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f366,plain,
    ( ~ m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f362,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f60,f117])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f362,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f361,f89])).

fof(f361,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f359,f97])).

fof(f359,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f358,f57])).

fof(f358,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | ~ v1_relat_1(X1)
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f356,f163])).

fof(f638,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f637,f52])).

fof(f637,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f636,f53])).

fof(f636,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f635,f54])).

fof(f635,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f634,f56])).

fof(f634,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f631,f72])).

fof(f631,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f630])).

fof(f630,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != sK3(sK2,k4_tmap_1(sK0,sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f629])).

fof(f629,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != sK3(sK2,k4_tmap_1(sK0,sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(superposition,[],[f507,f627])).

fof(f627,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f626,f52])).

fof(f626,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f625,f53])).

fof(f625,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f624,f54])).

fof(f624,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f623,f56])).

fof(f623,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f622,f72])).

fof(f622,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f621,f216])).

fof(f621,plain,
    ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f620,f607])).

fof(f607,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f590,f401])).

fof(f590,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f589,f52])).

fof(f589,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f588,f53])).

fof(f588,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f587,f54])).

fof(f587,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f586,f56])).

fof(f586,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f585,f72])).

fof(f585,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f584,f237])).

fof(f237,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f52])).

fof(f236,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f53])).

fof(f235,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f234,f54])).

fof(f234,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f56])).

fof(f233,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f232,f72])).

fof(f232,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f231,f113])).

fof(f231,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f230,f89])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f52])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f53])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f227,f54])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f226,f56])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f175,f72])).

fof(f175,plain,(
    ! [X3] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f113])).

fof(f169,plain,(
    ! [X3] :
      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f67,f163])).

fof(f584,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f583,f113])).

fof(f583,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f582])).

fof(f582,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f580,f202])).

fof(f202,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK2))
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f200,f97])).

fof(f200,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK2))
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f69,f57])).

fof(f580,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f579])).

fof(f579,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f576,f117])).

fof(f576,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f574,f107])).

fof(f574,plain,
    ( ~ m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f573,f237])).

fof(f573,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f572,f52])).

fof(f572,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f571,f53])).

fof(f571,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f570,f54])).

fof(f570,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f569,f56])).

fof(f569,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f327,f113])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_tmap_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(X0,X1)))
      | r1_tarski(sK2,k4_tmap_1(X0,X1))
      | sK3(sK2,k4_tmap_1(X0,X1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(X0,X1)))
      | ~ m1_subset_1(sK3(sK2,k4_tmap_1(X0,X1)),u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f204,f72])).

fof(f204,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(sK2,X2)
      | sK3(sK2,X2) = k1_funct_1(sK2,sK3(sK2,X2))
      | ~ m1_subset_1(sK3(sK2,X2),u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f202,f121])).

fof(f620,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f619,f600])).

fof(f600,plain,
    ( ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f590,f77])).

fof(f619,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f618,f113])).

fof(f618,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f617,f97])).

fof(f617,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f616,f57])).

fof(f616,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(superposition,[],[f70,f606])).

fof(f606,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f590,f374])).

fof(f374,plain,
    ( ~ r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f367,f77])).

fof(f367,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f362,f295])).

fof(f295,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f294,f117])).

fof(f294,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f293,f107])).

fof(f293,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f292,f55])).

fof(f292,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f291,f56])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | k1_funct_1(k4_tmap_1(sK0,X1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f290,f52])).

fof(f290,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | k1_funct_1(k4_tmap_1(sK0,X1),X0) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f54])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | k1_funct_1(k4_tmap_1(sK0,X1),X0) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | r1_tarski(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f507,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f506,f237])).

fof(f506,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f505,f97])).

fof(f505,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f504,f57])).

fof(f504,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f503,f113])).

fof(f503,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f70,f502])).

fof(f502,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f501,f52])).

fof(f501,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f500,f53])).

fof(f500,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f499,f54])).

fof(f499,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f498,f56])).

fof(f498,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f497,f72])).

fof(f497,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f496,f216])).

fof(f496,plain,
    ( ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f495,f484])).

fof(f484,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f481])).

fof(f481,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f471,f393])).

fof(f471,plain,
    ( ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f461,f77])).

fof(f461,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f460,f237])).

fof(f460,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f459,f52])).

fof(f459,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f458,f53])).

fof(f458,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f457,f54])).

fof(f457,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f456,f56])).

fof(f456,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1)))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f300,f113])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_tmap_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(X0,X1)))
      | sK3(sK2,k4_tmap_1(X0,X1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(X0,X1)))
      | k1_xboole_0 = u1_struct_0(sK0)
      | r1_tarski(sK2,k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f296,f72])).

fof(f296,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | sK3(sK2,X0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f295,f202])).

fof(f495,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f494,f471])).

fof(f494,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f493,f113])).

fof(f493,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f492,f97])).

fof(f492,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f491,f57])).

fof(f491,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(superposition,[],[f70,f483])).

fof(f483,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f482])).

fof(f482,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f471,f367])).

fof(f669,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f668,f649])).

fof(f649,plain,
    ( ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f648])).

fof(f648,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f638,f77])).

fof(f668,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f667,f113])).

fof(f667,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f666,f97])).

fof(f666,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f665,f57])).

fof(f665,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(superposition,[],[f70,f655])).

fof(f655,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f640])).

fof(f640,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f638,f374])).

fof(f61,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (14238)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (14245)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.49  % (14227)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (14227)Refutation not found, incomplete strategy% (14227)------------------------------
% 0.20/0.49  % (14227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14227)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (14227)Memory used [KB]: 10618
% 0.20/0.49  % (14227)Time elapsed: 0.074 s
% 0.20/0.49  % (14227)------------------------------
% 0.20/0.49  % (14227)------------------------------
% 0.20/0.49  % (14228)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (14234)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (14230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (14231)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (14241)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (14236)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (14249)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (14248)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (14229)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (14243)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (14237)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (14233)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (14234)Refutation not found, incomplete strategy% (14234)------------------------------
% 0.20/0.51  % (14234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14234)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14234)Memory used [KB]: 1791
% 0.20/0.51  % (14234)Time elapsed: 0.090 s
% 0.20/0.51  % (14234)------------------------------
% 0.20/0.51  % (14234)------------------------------
% 0.20/0.51  % (14252)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (14244)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (14239)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (14242)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (14240)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (14250)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (14232)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (14246)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (14235)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (14248)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f801,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f800,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f38,f37,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f14])).
% 0.20/0.53  fof(f14,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 0.20/0.53  fof(f800,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f799,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f799,plain,(
% 0.20/0.53    ~l1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f798,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f798,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f794,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f794,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f64,f765])).
% 0.20/0.53  fof(f765,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f677,f441])).
% 0.20/0.53  fof(f441,plain,(
% 0.20/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f439,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f439,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 0.20/0.53    inference(resolution,[],[f437,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f437,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,sK2,sK2)) )),
% 0.20/0.53    inference(resolution,[],[f436,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f436,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f435])).
% 0.20/0.53  fof(f435,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(equality_resolution,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) | r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(rectify,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).
% 0.20/0.53  fof(f677,plain,(
% 0.20/0.53    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f61,f676])).
% 0.20/0.53  fof(f676,plain,(
% 0.20/0.53    k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f675,f52])).
% 0.20/0.53  fof(f675,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f674,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f674,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f673,f54])).
% 0.20/0.53  fof(f673,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f672,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    m1_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f672,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f671,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 0.20/0.53  fof(f671,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f670,f216])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f215,f52])).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f214,f53])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f213,f54])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f212,f56])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f211,f72])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f210,f113])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    v1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f111,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(resolution,[],[f110,f56])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f109,f52])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f108,f54])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f74,f53])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f209,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f208,f52])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f207,f53])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = u1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f206,f54])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = u1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f205,f56])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f174,f72])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~r1_tarski(X2,k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f168,f113])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~r1_tarski(X2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f67,f163])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f126,f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f159,f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f111,f117])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    u1_struct_0(sK1) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(forward_demodulation,[],[f116,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f79,f59])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f114,f59])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(resolution,[],[f80,f58])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f158])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))),
% 0.20/0.53    inference(resolution,[],[f157,f80])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f156,f52])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f155,f54])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f154,f56])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f128,f53])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X3] : (~v2_pre_topc(X3) | ~m1_pre_topc(sK1,X3) | ~l1_pre_topc(X3) | v1_funct_2(k4_tmap_1(X3,sK1),k1_relat_1(sK2),u1_struct_0(X3)) | v2_struct_0(X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f73,f117])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f112,f117])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f111,f79])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(rectify,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).
% 0.20/0.53  fof(f670,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f669,f656])).
% 0.20/0.53  fof(f656,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f639])).
% 0.20/0.53  fof(f639,plain,(
% 0.20/0.53    k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f638,f401])).
% 0.20/0.53  fof(f401,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f393,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f390,f384])).
% 0.20/0.53  fof(f384,plain,(
% 0.20/0.53    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f383,f222])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f219])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f216,f182])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    u1_struct_0(sK1) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f180,f112])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f179,f111])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f176])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(resolution,[],[f171,f80])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f170,f117])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    u1_struct_0(sK1) != k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f165])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    u1_struct_0(sK1) != k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f145,f163])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    u1_struct_0(sK1) != k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(forward_demodulation,[],[f141,f112])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    u1_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(resolution,[],[f82,f111])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f381,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f78,f59])).
% 0.20/0.53  fof(f381,plain,(
% 0.20/0.53    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~v1_relat_1(sK2) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(u1_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f357,f57])).
% 0.20/0.53  fof(f357,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),u1_struct_0(sK1)) | ~v1_relat_1(X0) | r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~r1_tarski(u1_struct_0(sK1),k1_relat_1(X0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f356,f182])).
% 0.20/0.53  fof(f356,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f355,f52])).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k4_tmap_1(sK0,sK1),X0) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1))) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f354,f53])).
% 0.20/0.53  fof(f354,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k4_tmap_1(sK0,sK1),X0) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f353,f54])).
% 0.20/0.53  fof(f353,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k4_tmap_1(sK0,sK1),X0) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f352,f56])).
% 0.20/0.53  fof(f352,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k4_tmap_1(sK0,sK1),X0) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X0),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f201,f113])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    ( ! [X2,X3,X1] : (~v1_relat_1(k4_tmap_1(X1,X2)) | ~r1_tarski(k1_relat_1(k4_tmap_1(X1,X2)),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | r1_tarski(k4_tmap_1(X1,X2),X3) | r2_hidden(sK3(k4_tmap_1(X1,X2),X3),k1_relat_1(k4_tmap_1(X1,X2))) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.53    inference(resolution,[],[f69,f72])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f390,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 0.20/0.53    inference(resolution,[],[f366,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1))) )),
% 0.20/0.53    inference(resolution,[],[f106,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f105,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(resolution,[],[f104,f56])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f103,f52])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f66,f54])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.20/0.53  fof(f366,plain,(
% 0.20/0.53    ~m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f365])).
% 0.20/0.53  fof(f365,plain,(
% 0.20/0.53    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f362,f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f60,f117])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f362,plain,(
% 0.20/0.53    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f361,f89])).
% 0.20/0.53  fof(f361,plain,(
% 0.20/0.53    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f359,f97])).
% 0.20/0.53  fof(f359,plain,(
% 0.20/0.53    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f358,f57])).
% 0.20/0.53  fof(f358,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_funct_1(X1) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | ~v1_relat_1(X1) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f356,f163])).
% 0.20/0.53  fof(f638,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f637,f52])).
% 0.20/0.53  fof(f637,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f636,f53])).
% 0.20/0.53  fof(f636,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f635,f54])).
% 0.20/0.53  fof(f635,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f634,f56])).
% 0.20/0.53  fof(f634,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f631,f72])).
% 0.20/0.53  fof(f631,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f630])).
% 0.20/0.53  fof(f630,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != sK3(sK2,k4_tmap_1(sK0,sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f629])).
% 0.20/0.53  fof(f629,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != sK3(sK2,k4_tmap_1(sK0,sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(superposition,[],[f507,f627])).
% 0.20/0.53  fof(f627,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f626,f52])).
% 0.20/0.53  fof(f626,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2 | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f625,f53])).
% 0.20/0.53  fof(f625,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f624,f54])).
% 0.20/0.53  fof(f624,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f623,f56])).
% 0.20/0.53  fof(f623,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2 | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f622,f72])).
% 0.20/0.53  fof(f622,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f621,f216])).
% 0.20/0.53  fof(f621,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f620,f607])).
% 0.20/0.53  fof(f607,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f591])).
% 0.20/0.53  fof(f591,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f590,f401])).
% 0.20/0.53  fof(f590,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f589,f52])).
% 0.20/0.53  fof(f589,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f588,f53])).
% 0.20/0.53  fof(f588,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f587,f54])).
% 0.20/0.53  fof(f587,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f586,f56])).
% 0.20/0.53  fof(f586,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f585,f72])).
% 0.20/0.53  fof(f585,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f584,f237])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f236,f52])).
% 0.20/0.53  fof(f236,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f235,f53])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f234,f54])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f233,f56])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f232,f72])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f231,f113])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f230,f89])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f229,f52])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f228,f53])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_xboole_0 = u1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f227,f54])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_xboole_0 = u1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f226,f56])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f175,f72])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    ( ! [X3] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~r1_tarski(k4_tmap_1(sK0,sK1),X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f113])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ( ! [X3] : (r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~r1_tarski(k4_tmap_1(sK0,sK1),X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f67,f163])).
% 0.20/0.53  fof(f584,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f583,f113])).
% 0.20/0.53  fof(f583,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f582])).
% 0.20/0.53  fof(f582,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f580,f202])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(sK2,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f200,f97])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(resolution,[],[f69,f57])).
% 0.20/0.53  fof(f580,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f579])).
% 0.20/0.53  fof(f579,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f576,f117])).
% 0.20/0.53  fof(f576,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(resolution,[],[f574,f107])).
% 0.20/0.53  fof(f574,plain,(
% 0.20/0.53    ~m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f573,f237])).
% 0.20/0.53  fof(f573,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f572,f52])).
% 0.20/0.53  fof(f572,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f571,f53])).
% 0.20/0.53  fof(f571,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f570,f54])).
% 0.20/0.53  fof(f570,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f569,f56])).
% 0.20/0.53  fof(f569,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f327,f113])).
% 0.20/0.53  fof(f327,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(k4_tmap_1(X0,X1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(X0,X1))) | r1_tarski(sK2,k4_tmap_1(X0,X1)) | sK3(sK2,k4_tmap_1(X0,X1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(X0,X1))) | ~m1_subset_1(sK3(sK2,k4_tmap_1(X0,X1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f204,f72])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_funct_1(X2) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(sK2,X2) | sK3(sK2,X2) = k1_funct_1(sK2,sK3(sK2,X2)) | ~m1_subset_1(sK3(sK2,X2),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f202,f121])).
% 0.20/0.53  fof(f620,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f619,f600])).
% 0.20/0.53  fof(f600,plain,(
% 0.20/0.53    ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f590,f77])).
% 0.20/0.53  fof(f619,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f618,f113])).
% 0.20/0.53  fof(f618,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f617,f97])).
% 0.20/0.53  fof(f617,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f616,f57])).
% 0.20/0.53  fof(f616,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(superposition,[],[f70,f606])).
% 0.20/0.53  fof(f606,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f592])).
% 0.20/0.53  fof(f592,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f590,f374])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f367,f77])).
% 0.20/0.53  fof(f367,plain,(
% 0.20/0.53    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f363])).
% 0.20/0.53  fof(f363,plain,(
% 0.20/0.53    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f362,f295])).
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(superposition,[],[f294,f117])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f293,f107])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f292,f55])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 0.20/0.53    inference(resolution,[],[f291,f56])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(X1)) | v2_struct_0(X1) | k1_funct_1(k4_tmap_1(sK0,X1),X0) = X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f290,f52])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k1_funct_1(k4_tmap_1(sK0,X1),X0) = X0 | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f289,f54])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | k1_funct_1(k4_tmap_1(sK0,X1),X0) = X0 | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f65,f53])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | r1_tarski(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f507,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f506,f237])).
% 0.20/0.53  fof(f506,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f505,f97])).
% 0.20/0.53  fof(f505,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(sK2) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f504,f57])).
% 0.20/0.53  fof(f504,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f503,f113])).
% 0.20/0.53  fof(f503,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f70,f502])).
% 0.20/0.53  fof(f502,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f501,f52])).
% 0.20/0.53  fof(f501,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f500,f53])).
% 0.20/0.53  fof(f500,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f499,f54])).
% 0.20/0.53  fof(f499,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f498,f56])).
% 0.20/0.53  fof(f498,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f497,f72])).
% 0.20/0.53  fof(f497,plain,(
% 0.20/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f496,f216])).
% 0.20/0.53  fof(f496,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f495,f484])).
% 0.20/0.53  fof(f484,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f481])).
% 0.20/0.53  fof(f481,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f471,f393])).
% 0.20/0.53  fof(f471,plain,(
% 0.20/0.53    ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f461,f77])).
% 0.20/0.53  fof(f461,plain,(
% 0.20/0.53    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f460,f237])).
% 0.20/0.53  fof(f460,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f459,f52])).
% 0.20/0.53  fof(f459,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f458,f53])).
% 0.20/0.53  fof(f458,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f457,f54])).
% 0.20/0.53  fof(f457,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f456,f56])).
% 0.20/0.53  fof(f456,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(sK0,sK1))) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f300,f113])).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(k4_tmap_1(X0,X1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k4_tmap_1(X0,X1))) | sK3(sK2,k4_tmap_1(X0,X1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(X0,X1))) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f296,f72])).
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | k1_xboole_0 = u1_struct_0(sK0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | sK3(sK2,X0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,X0)) | ~v1_relat_1(X0) | r1_tarski(sK2,X0)) )),
% 0.20/0.53    inference(resolution,[],[f295,f202])).
% 0.20/0.53  fof(f495,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f494,f471])).
% 0.20/0.53  fof(f494,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f493,f113])).
% 0.20/0.53  fof(f493,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f492,f97])).
% 0.20/0.53  fof(f492,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f491,f57])).
% 0.20/0.53  fof(f491,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(superposition,[],[f70,f483])).
% 0.20/0.53  fof(f483,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f482])).
% 0.20/0.53  fof(f482,plain,(
% 0.20/0.53    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.20/0.53    inference(resolution,[],[f471,f367])).
% 0.20/0.53  fof(f669,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f668,f649])).
% 0.20/0.53  fof(f649,plain,(
% 0.20/0.53    ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f648])).
% 0.20/0.53  fof(f648,plain,(
% 0.20/0.53    k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f638,f77])).
% 0.20/0.53  fof(f668,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f667,f113])).
% 0.20/0.53  fof(f667,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f666,f97])).
% 0.20/0.53  fof(f666,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(subsumption_resolution,[],[f665,f57])).
% 0.20/0.53  fof(f665,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~r1_tarski(k1_relat_1(k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(superposition,[],[f70,f655])).
% 0.20/0.53  fof(f655,plain,(
% 0.20/0.53    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f640])).
% 0.20/0.53  fof(f640,plain,(
% 0.20/0.53    k4_tmap_1(sK0,sK1) = sK2 | k1_xboole_0 = u1_struct_0(sK0) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = u1_struct_0(sK0) | k4_tmap_1(sK0,sK1) = sK2),
% 0.20/0.53    inference(resolution,[],[f638,f374])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (14248)------------------------------
% 0.20/0.53  % (14248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14248)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (14248)Memory used [KB]: 6780
% 0.20/0.53  % (14248)Time elapsed: 0.125 s
% 0.20/0.53  % (14248)------------------------------
% 0.20/0.53  % (14248)------------------------------
% 0.20/0.54  % (14226)Success in time 0.178 s
%------------------------------------------------------------------------------
