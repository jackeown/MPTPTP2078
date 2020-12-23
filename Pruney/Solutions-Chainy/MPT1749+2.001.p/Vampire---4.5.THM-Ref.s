%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  202 (4612 expanded)
%              Number of leaves         :   23 (2171 expanded)
%              Depth                    :   68
%              Number of atoms          : 1021 (78504 expanded)
%              Number of equality atoms :   96 (5730 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f62])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f47,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(X2))
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(sK2))
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                | ~ r2_hidden(X5,u1_struct_0(sK2))
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
              | ~ r2_hidden(X5,u1_struct_0(sK2))
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
        & ! [X5] :
            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
            | ~ r2_hidden(X5,u1_struct_0(sK2))
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
      & ! [X5] :
          ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,u1_struct_0(sK2))
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f324,plain,(
    ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f323,f64])).

fof(f64,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f323,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f322,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f322,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f321,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f320,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f320,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f319,f62])).

fof(f319,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f318,f73])).

fof(f318,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f317,f73])).

fof(f317,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f238,f315])).

fof(f315,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f312,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f312,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f311,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f311,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f309,f64])).

fof(f309,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f307,f62])).

fof(f307,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f305,f75])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f305,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X0) ) ),
    inference(resolution,[],[f304,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X0) ) ),
    inference(resolution,[],[f303,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f302,f80])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X2) ) ),
    inference(resolution,[],[f301,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))
      | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f300,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f298,f278])).

fof(f278,plain,
    ( k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f276,f78])).

fof(f276,plain,
    ( k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) ),
    inference(superposition,[],[f275,f71])).

fof(f71,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f275,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f274,f62])).

fof(f274,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ),
    inference(resolution,[],[f261,f64])).

fof(f261,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ) ),
    inference(resolution,[],[f260,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f102,f80])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f101,f64])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f99,f62])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f98,f75])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f97,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f96,f86])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f95,f67])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f93,f66])).

fof(f66,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK3,X1,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f260,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f259,f74])).

fof(f259,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f258,f59])).

fof(f258,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f257,f73])).

fof(f257,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f256,f62])).

fof(f256,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f255,f73])).

fof(f255,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f238,f73])).

fof(f298,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f297,f62])).

fof(f297,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f296,f64])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f295,f260])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f294,f80])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f293,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f293,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ) ),
    inference(subsumption_resolution,[],[f292,f65])).

fof(f292,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f291,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f291,plain,(
    ! [X0] :
      ( k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f290,f74])).

fof(f290,plain,
    ( ~ l1_pre_topc(sK2)
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ),
    inference(subsumption_resolution,[],[f289,f59])).

fof(f289,plain,
    ( k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f288,f73])).

fof(f288,plain,
    ( ~ l1_struct_0(sK0)
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f287,f62])).

fof(f287,plain,
    ( ~ l1_struct_0(sK0)
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f286,f73])).

fof(f286,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f285,f73])).

fof(f285,plain,
    ( ~ l1_struct_0(sK2)
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f284,f229])).

fof(f229,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f228,f65])).

fof(f228,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f227,f66])).

fof(f227,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f224,f67])).

fof(f224,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f91,f186])).

fof(f186,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f185,f65])).

fof(f185,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f183,f67])).

fof(f183,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f180,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f180,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f179,f65])).

fof(f179,plain,
    ( ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f177,f67])).

fof(f177,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f174,f66])).

fof(f174,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X0)
      | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f173,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f59])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f170,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f169,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f168,f61])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f167,f62])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f77,f64])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f284,plain,
    ( k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f252,f234])).

fof(f234,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f233,f65])).

fof(f233,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f232,f66])).

fof(f232,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f225,f67])).

fof(f225,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f90,f186])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f252,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f221,f250])).

fof(f250,plain,(
    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f249,f62])).

fof(f249,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f247,f64])).

fof(f247,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f245,f74])).

fof(f245,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f244,f59])).

fof(f244,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f242,f73])).

fof(f242,plain,
    ( ~ l1_struct_0(sK0)
    | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f241,f62])).

fof(f241,plain,
    ( ~ l1_struct_0(sK0)
    | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f239,f73])).

fof(f239,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f237,f73])).

fof(f237,plain,
    ( ~ l1_struct_0(sK2)
    | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f236,f65])).

fof(f236,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f235,f66])).

fof(f235,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f226,f67])).

fof(f226,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f89,f186])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f221,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f220,f186])).

fof(f220,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(forward_demodulation,[],[f219,f186])).

fof(f219,plain,
    ( k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(forward_demodulation,[],[f199,f186])).

fof(f199,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(backward_demodulation,[],[f164,f186])).

fof(f164,plain,
    ( k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f163,f68])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f163,plain,
    ( k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f162,f69])).

fof(f69,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f162,plain,
    ( k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f159,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f159,plain,
    ( k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(resolution,[],[f85,f72])).

fof(f72,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
                & m1_subset_1(sK6(X0,X2,X3),X0) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).

fof(f55,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
        & m1_subset_1(sK6(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f238,plain,
    ( ~ l1_struct_0(sK2)
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f230,f237])).

fof(f230,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f205,f229])).

fof(f205,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f204,f186])).

fof(f204,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f189,f186])).

fof(f189,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(backward_demodulation,[],[f132,f186])).

fof(f132,plain,
    ( ~ l1_struct_0(sK2)
    | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f131,f65])).

fof(f131,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f130,f66])).

fof(f130,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f129,f67])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f122,f90])).

fof(f122,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f121,f68])).

fof(f121,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f120,f69])).

fof(f120,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f119,f70])).

fof(f119,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(resolution,[],[f84,f72])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK6(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (26114)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.46  % (26130)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.46  % (26125)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.46  % (26117)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.46  % (26122)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.48  % (26117)Refutation not found, incomplete strategy% (26117)------------------------------
% 0.20/0.48  % (26117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26117)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26117)Memory used [KB]: 10874
% 0.20/0.48  % (26117)Time elapsed: 0.071 s
% 0.20/0.48  % (26117)------------------------------
% 0.20/0.48  % (26117)------------------------------
% 0.20/0.49  % (26113)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (26115)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (26109)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (26121)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (26131)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (26129)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (26126)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (26111)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (26128)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (26123)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (26120)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (26118)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (26112)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.52  % (26119)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (26112)Refutation not found, incomplete strategy% (26112)------------------------------
% 0.20/0.52  % (26112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26112)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26112)Memory used [KB]: 10746
% 0.20/0.52  % (26112)Time elapsed: 0.102 s
% 0.20/0.52  % (26112)------------------------------
% 0.20/0.52  % (26112)------------------------------
% 0.20/0.53  % (26127)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.54  % (26132)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.54  % (26110)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.54  % (26128)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f325,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f324,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    l1_pre_topc(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f47,f46,f45,f44,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 0.20/0.54  fof(f324,plain,(
% 0.20/0.54    ~l1_pre_topc(sK1)),
% 0.20/0.54    inference(resolution,[],[f323,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    m1_pre_topc(sK2,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f323,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(resolution,[],[f322,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.54  fof(f322,plain,(
% 0.20/0.54    ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f321,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f321,plain,(
% 0.20/0.54    ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.54    inference(resolution,[],[f320,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.54  fof(f320,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f319,f62])).
% 0.20/0.54  fof(f319,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.20/0.54    inference(resolution,[],[f318,f73])).
% 0.20/0.54  fof(f318,plain,(
% 0.20/0.54    ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(resolution,[],[f317,f73])).
% 0.20/0.54  fof(f317,plain,(
% 0.20/0.54    ~l1_struct_0(sK2) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f238,f315])).
% 0.20/0.54  fof(f315,plain,(
% 0.20/0.54    ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f312,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ~v2_struct_0(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f312,plain,(
% 0.20/0.54    ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.20/0.54    inference(resolution,[],[f311,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.54  fof(f311,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f310])).
% 0.20/0.54  fof(f310,plain,(
% 0.20/0.54    ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.54    inference(resolution,[],[f309,f64])).
% 0.20/0.54  fof(f309,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f307,f62])).
% 0.20/0.54  fof(f307,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f305,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.54  fof(f305,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | v1_xboole_0(X0) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X0)) )),
% 0.20/0.54    inference(resolution,[],[f304,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f304,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | v1_xboole_0(X0) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X0)) )),
% 0.20/0.54    inference(resolution,[],[f303,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))) )),
% 0.20/0.54    inference(resolution,[],[f302,f80])).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),X2)) )),
% 0.20/0.54    inference(resolution,[],[f301,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f300,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(rectify,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f300,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(u1_struct_0(sK2)) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f299])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(u1_struct_0(sK2)) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))) )),
% 0.20/0.54    inference(superposition,[],[f298,f278])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f276,f78])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | v1_xboole_0(u1_struct_0(sK2)) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))),
% 0.20/0.54    inference(superposition,[],[f275,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f275,plain,(
% 0.20/0.54    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f274,f62])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    ~l1_pre_topc(sK1) | v1_xboole_0(u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))),
% 0.20/0.54    inference(resolution,[],[f261,f64])).
% 0.20/0.54  fof(f261,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | v1_xboole_0(u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))) )),
% 0.20/0.54    inference(resolution,[],[f260,f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.54    inference(resolution,[],[f102,f80])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.54    inference(resolution,[],[f101,f64])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,sK1) | ~r2_hidden(X0,u1_struct_0(X1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f99,f62])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f98,f75])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f97,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f96,f86])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f95,f67])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.20/0.54    inference(resolution,[],[f93,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,X1,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(X1)) )),
% 0.20/0.54    inference(resolution,[],[f88,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    v1_funct_1(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(resolution,[],[f259,f74])).
% 0.20/0.54  fof(f259,plain,(
% 0.20/0.54    ~l1_pre_topc(sK2) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f258,f59])).
% 0.20/0.54  fof(f258,plain,(
% 0.20/0.54    m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.54    inference(resolution,[],[f257,f73])).
% 0.20/0.54  fof(f257,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f256,f62])).
% 0.20/0.54  fof(f256,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.20/0.54    inference(resolution,[],[f255,f73])).
% 0.20/0.54  fof(f255,plain,(
% 0.20/0.54    ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(resolution,[],[f238,f73])).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f297,f62])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~l1_pre_topc(sK1) | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.54    inference(resolution,[],[f296,f64])).
% 0.20/0.54  fof(f296,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f295,f260])).
% 0.20/0.54  fof(f295,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))) )),
% 0.20/0.54    inference(resolution,[],[f294,f80])).
% 0.20/0.54  fof(f294,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.54    inference(resolution,[],[f293,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_relat_1(sK3) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f292,f65])).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(sK3,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~r2_hidden(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.54    inference(superposition,[],[f291,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).
% 0.20/0.54  fof(f291,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(resolution,[],[f290,f74])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    ~l1_pre_topc(sK2) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))),
% 0.20/0.54    inference(subsumption_resolution,[],[f289,f59])).
% 0.20/0.54  fof(f289,plain,(
% 0.20/0.54    k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.54    inference(resolution,[],[f288,f73])).
% 0.20/0.54  fof(f288,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f287,f62])).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.20/0.54    inference(resolution,[],[f286,f73])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(resolution,[],[f285,f73])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    ~l1_struct_0(sK2) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f284,f229])).
% 0.20/0.54  fof(f229,plain,(
% 0.20/0.54    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f228,f65])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK2) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f227,f66])).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f224,f67])).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(superposition,[],[f91,f186])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f185,f65])).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | ~v1_funct_1(sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f183,f67])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK3)),
% 0.20/0.55    inference(superposition,[],[f180,f92])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f179,f65])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f177,f67])).
% 0.20/0.55  fof(f177,plain,(
% 0.20/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.20/0.55    inference(resolution,[],[f174,f66])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f173,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ~v2_struct_0(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) | v2_struct_0(sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f171,f59])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) | v2_struct_0(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f170,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    v2_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2)) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f169,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ~v2_struct_0(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f168,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    v2_pre_topc(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f167,f62])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.55    inference(resolution,[],[f77,f64])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(resolution,[],[f252,f234])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f233,f65])).
% 0.20/0.55  fof(f233,plain,(
% 0.20/0.55    v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_struct_0(sK2) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f232,f66])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f225,f67])).
% 0.20/0.55  fof(f225,plain,(
% 0.20/0.55    v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(superposition,[],[f90,f186])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.20/0.55    inference(subsumption_resolution,[],[f221,f250])).
% 0.20/0.55  fof(f250,plain,(
% 0.20/0.55    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f249,f62])).
% 0.20/0.55  fof(f249,plain,(
% 0.20/0.55    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK1)),
% 0.20/0.55    inference(resolution,[],[f247,f64])).
% 0.20/0.55  fof(f247,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_pre_topc(sK2,X0) | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(resolution,[],[f245,f74])).
% 0.20/0.55  fof(f245,plain,(
% 0.20/0.55    ~l1_pre_topc(sK2) | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f244,f59])).
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.55    inference(resolution,[],[f242,f73])).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    ~l1_struct_0(sK0) | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f241,f62])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ~l1_struct_0(sK0) | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.20/0.55    inference(resolution,[],[f239,f73])).
% 0.20/0.55  fof(f239,plain,(
% 0.20/0.55    ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.20/0.55    inference(resolution,[],[f237,f73])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    ~l1_struct_0(sK2) | v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f236,f65])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_struct_0(sK2) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f235,f66])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f226,f67])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(superposition,[],[f89,f186])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    ~v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.20/0.55    inference(forward_demodulation,[],[f220,f186])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(forward_demodulation,[],[f219,f186])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(forward_demodulation,[],[f199,f186])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(backward_demodulation,[],[f164,f186])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f163,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    v1_funct_1(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f162,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f159,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    k1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) != k1_funct_1(sK4,sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(resolution,[],[f85,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3)) & m1_subset_1(sK6(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3)) & m1_subset_1(sK6(X0,X2,X3),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(rectify,[],[f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(nnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ~l1_struct_0(sK2) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f230,f237])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ~v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f205,f229])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(forward_demodulation,[],[f204,f186])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    ~v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(forward_demodulation,[],[f189,f186])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    m1_subset_1(sK6(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(backward_demodulation,[],[f132,f186])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    ~l1_struct_0(sK2) | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f131,f65])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~l1_struct_0(sK2) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f130,f66])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~l1_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f129,f67])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~l1_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~l1_struct_0(sK1)),
% 0.20/0.55    inference(resolution,[],[f122,f90])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f121,f68])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f120,f69])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f119,f70])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    m1_subset_1(sK6(u1_struct_0(sK2),k2_tmap_1(sK1,sK0,sK3,sK2),sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.55    inference(resolution,[],[f84,f72])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK6(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f56])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (26128)------------------------------
% 0.20/0.55  % (26128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26128)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (26128)Memory used [KB]: 6652
% 0.20/0.55  % (26128)Time elapsed: 0.137 s
% 0.20/0.55  % (26128)------------------------------
% 0.20/0.55  % (26128)------------------------------
% 0.20/0.55  % (26108)Success in time 0.192 s
%------------------------------------------------------------------------------
