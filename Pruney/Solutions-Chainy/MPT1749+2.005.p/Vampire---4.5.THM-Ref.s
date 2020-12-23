%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 802 expanded)
%              Number of leaves         :   15 ( 369 expanded)
%              Depth                    :   63
%              Number of atoms          :  998 (13365 expanded)
%              Number of equality atoms :  145 (1019 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(resolution,[],[f145,f47])).

fof(f47,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f27,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f145,plain,(
    ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f143,f75])).

fof(f75,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK4,X2,X3)
      | r2_funct_2(X2,X3,sK4,sK4) ) ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
        & m1_subset_1(sK6(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f143,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    inference(backward_demodulation,[],[f50,f142])).

fof(f142,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f141,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f141,plain,
    ( ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f140,f46])).

fof(f140,plain,
    ( ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f139,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f138,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f138,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f137,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f137,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f136,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f136,plain,
    ( v2_struct_0(sK1)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f135,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f135,plain,
    ( v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f134,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f133,f40])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f132,f54])).

fof(f132,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f131,f57])).

fof(f131,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f130,f40])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f129,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f128,f54])).

fof(f128,plain,
    ( ~ l1_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f127,f57])).

fof(f127,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f126,f44])).

fof(f44,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f126,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f125,f47])).

fof(f125,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f124,f40])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f123,f42])).

fof(f123,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f122,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

% (28717)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f122,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f121,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f120,f48])).

fof(f120,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(forward_demodulation,[],[f118,f88])).

fof(f88,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f86,f43])).

fof(f86,plain,
    ( ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f85,f35])).

fof(f85,plain,
    ( v2_struct_0(sK0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f84,f38])).

fof(f84,plain,
    ( v2_struct_0(sK1)
    | ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f83,f44])).

fof(f83,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f82,f37])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f79,f45])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | k2_tmap_1(sK1,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f78,f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | k2_tmap_1(sK1,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f118,plain,
    ( sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(superposition,[],[f53,f116])).

fof(f116,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f115,f43])).

fof(f115,plain,
    ( ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) ),
    inference(resolution,[],[f114,f37])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f113,f54])).

fof(f113,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f112,f35])).

fof(f112,plain,
    ( v2_struct_0(sK0)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f111,f38])).

fof(f111,plain,
    ( v2_struct_0(sK1)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f41])).

fof(f110,plain,
    ( v2_struct_0(sK2)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f109,f57])).

fof(f109,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | v2_struct_0(sK2)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f108,f40])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | v1_xboole_0(u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f107,f54])).

fof(f107,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | v1_xboole_0(u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f106,f57])).

fof(f106,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f105,f40])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f104,f62])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f103,f54])).

fof(f103,plain,
    ( ~ l1_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f102,f57])).

fof(f102,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(resolution,[],[f101,f45])).

fof(f101,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    inference(forward_demodulation,[],[f100,f88])).

fof(f100,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f99,f44])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK0))
      | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f96,f47])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2)) = X2
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) ) ),
    inference(resolution,[],[f95,f40])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2)) = X2
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) ) ),
    inference(resolution,[],[f94,f42])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK2,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2)) = X2
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f93,f56])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X0,X1,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X0,X1,u1_struct_0(sK2),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),X0)
      | ~ v1_funct_1(X2)
      | k2_partfun1(u1_struct_0(sK1),X0,X1,u1_struct_0(sK2)) = X2 ) ),
    inference(resolution,[],[f92,f40])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f91,f42])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK2,sK1)
      | ~ v1_funct_1(X0)
      | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X0)
      | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ m1_pre_topc(sK2,sK1)
      | ~ l1_pre_topc(sK1)
      | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
                        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f29])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

% (28720)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(u1_struct_0(X2),X1,X3,u1_struct_0(sK2),X0),u1_struct_0(sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X0)
      | k2_partfun1(u1_struct_0(X2),X1,X3,u1_struct_0(sK2)) = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X2),X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(X2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(X2),X1,X3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(X2),X1,X3,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X3)
      | k2_partfun1(X0,X1,X2,u1_struct_0(sK2)) = X3
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(X0,X1,X2,u1_struct_0(sK2),X3)) = k1_funct_1(sK4,sK5(X0,X1,X2,u1_struct_0(sK2),X3))
      | ~ m1_subset_1(sK5(X0,X1,X2,u1_struct_0(sK2),X3),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f52,f49])).

fof(f49,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (28730)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.47  % (28722)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.48  % (28722)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(resolution,[],[f145,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f27,f26,f25,f24,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f143,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f70,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK4,X2,X3) | r2_funct_2(X2,X3,sK4,sK4)) )),
% 0.20/0.48    inference(resolution,[],[f68,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v1_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(equality_resolution,[],[f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3)) | r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3)) & m1_subset_1(sK6(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3)) & m1_subset_1(sK6(X0,X2,X3),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(rectify,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)),
% 0.20/0.48    inference(backward_demodulation,[],[f50,f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f141,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f140,f46])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f139,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f138,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f137,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v1_funct_1(sK4) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f136,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    v2_struct_0(sK1) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK4) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f135,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    v2_struct_0(sK2) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f134,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f133,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    l1_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f132,f54])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~l1_struct_0(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f131,f57])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK1)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK4)),
% 0.20/0.48    inference(resolution,[],[f130,f40])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.48    inference(resolution,[],[f129,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.20/0.48    inference(resolution,[],[f55,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    m1_pre_topc(sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~l1_pre_topc(sK2) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f128,f54])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~l1_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2)),
% 0.20/0.48    inference(resolution,[],[f127,f57])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f126,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.48    inference(resolution,[],[f125,f47])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.48    inference(resolution,[],[f124,f40])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | v1_xboole_0(u1_struct_0(sK2)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f123,f42])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK2)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1)),
% 0.20/0.48    inference(resolution,[],[f122,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.48  % (28717)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK2)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.48    inference(resolution,[],[f121,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.48    inference(resolution,[],[f120,f48])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(forward_demodulation,[],[f118,f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.20/0.48    inference(resolution,[],[f86,f43])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.20/0.48    inference(resolution,[],[f85,f35])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    v2_struct_0(sK0) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f84,f38])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    v2_struct_0(sK1) | ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f83,f44])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f82,f37])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f80,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f79,f45])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | k2_tmap_1(sK1,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) | v2_struct_0(sK1)) )),
% 0.20/0.48    inference(resolution,[],[f78,f40])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | k2_tmap_1(sK1,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) | v2_struct_0(sK1)) )),
% 0.20/0.48    inference(resolution,[],[f74,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v2_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2)) | v2_struct_0(sK1)) )),
% 0.20/0.48    inference(resolution,[],[f58,f42])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f117])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(superposition,[],[f53,f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f115,f43])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))),
% 0.20/0.48    inference(resolution,[],[f114,f37])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f113,f54])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | ~v1_funct_1(sK3) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f112,f35])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    v2_struct_0(sK0) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.48    inference(resolution,[],[f111,f38])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    v2_struct_0(sK1) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f110,f41])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    v2_struct_0(sK2) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f109,f57])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | v2_struct_0(sK2) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f108,f40])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | v1_xboole_0(u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f107,f54])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ~l1_struct_0(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK2) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | v1_xboole_0(u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | v2_struct_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f106,f57])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK1)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f105,f40])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f104,f62])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~l1_pre_topc(sK2) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.48    inference(resolution,[],[f103,f54])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~l1_struct_0(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 | ~v1_funct_1(sK3) | v2_struct_0(sK2)),
% 0.20/0.48    inference(resolution,[],[f102,f57])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.49    inference(resolution,[],[f101,f45])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK2)) | k2_tmap_1(sK1,sK0,sK3,sK2) = sK4),
% 0.20/0.49    inference(forward_demodulation,[],[f100,f88])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.49    inference(resolution,[],[f99,f44])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) )),
% 0.20/0.49    inference(resolution,[],[f98,f46])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) )),
% 0.20/0.49    inference(resolution,[],[f97,f48])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2),sK4)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) )),
% 0.20/0.49    inference(resolution,[],[f96,f47])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(sK2),X1) | ~v1_funct_1(X0) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X0,u1_struct_0(sK1),X1) | ~v1_funct_1(X2) | k2_partfun1(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2)) = X2 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))) )),
% 0.20/0.49    inference(resolution,[],[f95,f40])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | ~v1_funct_2(X0,u1_struct_0(sK1),X1) | ~v1_funct_1(X0) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X2,u1_struct_0(sK2),X1) | ~v1_funct_1(X2) | k2_partfun1(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2)) = X2 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))) )),
% 0.20/0.49    inference(resolution,[],[f94,f42])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) | ~v1_funct_2(X0,u1_struct_0(sK1),X1) | ~v1_funct_1(X0) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X2,u1_struct_0(sK2),X1) | ~v1_funct_1(X2) | k2_partfun1(u1_struct_0(sK1),X1,X0,u1_struct_0(sK2)) = X2 | v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK1)) )),
% 0.20/0.49    inference(resolution,[],[f93,f56])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))) | ~v1_funct_2(X1,u1_struct_0(sK1),X0) | ~v1_funct_1(X1) | v1_xboole_0(X0) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK4,sK5(u1_struct_0(sK1),X0,X1,u1_struct_0(sK2),X2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X0,X1,u1_struct_0(sK2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) | ~v1_funct_2(X2,u1_struct_0(sK2),X0) | ~v1_funct_1(X2) | k2_partfun1(u1_struct_0(sK1),X0,X1,u1_struct_0(sK2)) = X2) )),
% 0.20/0.49    inference(resolution,[],[f92,f40])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) | ~v1_funct_2(X2,u1_struct_0(sK1),X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X0,u1_struct_0(sK2),X1) | ~v1_funct_1(X0) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.49    inference(resolution,[],[f91,f42])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(sK2,sK1) | ~v1_funct_1(X0) | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) | ~v1_funct_2(X2,u1_struct_0(sK1),X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X0,u1_struct_0(sK2),X1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X0,u1_struct_0(sK2),X1) | ~v1_funct_1(X0) | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) | ~v1_funct_2(X2,u1_struct_0(sK1),X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X0,u1_struct_0(sK2),X1) | ~v1_funct_1(X0) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) | ~v1_funct_2(X2,u1_struct_0(sK1),X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f89,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) | k2_partfun1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | (k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4)) & r2_hidden(sK5(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) => (k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4)) & r2_hidden(sK5(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  % (28720)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : ((k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3)) & m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X4,X3,X1) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,X0) => (r2_hidden(X5,X3) => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5))) => k2_partfun1(X0,X1,X2,X3) = X4))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(u1_struct_0(X2),X1,X3,u1_struct_0(sK2),X0),u1_struct_0(sK1)) | ~v1_funct_2(X0,u1_struct_0(sK2),X1) | ~v1_funct_1(X0) | k2_partfun1(u1_struct_0(X2),X1,X3,u1_struct_0(sK2)) = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X1))) | ~v1_funct_2(X3,u1_struct_0(X2),X1) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(X2)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(X2),X1,X3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(X2),X1,X3,u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2)) )),
% 0.20/0.49    inference(resolution,[],[f87,f56])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) | ~v1_funct_2(X3,u1_struct_0(sK2),X1) | ~v1_funct_1(X3) | k2_partfun1(X0,X1,X2,u1_struct_0(sK2)) = X3 | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(X0,X1,X2,u1_struct_0(sK2),X3)) = k1_funct_1(sK4,sK5(X0,X1,X2,u1_struct_0(sK2),X3)) | ~m1_subset_1(sK5(X0,X1,X2,u1_struct_0(sK2),X3),u1_struct_0(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f52,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X5] : (~r2_hidden(X5,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X2,X3,X4),X3) | k2_partfun1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4)) | k2_partfun1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (28722)------------------------------
% 0.20/0.49  % (28722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28722)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (28722)Memory used [KB]: 1918
% 0.20/0.49  % (28722)Time elapsed: 0.076 s
% 0.20/0.49  % (28722)------------------------------
% 0.20/0.49  % (28722)------------------------------
% 0.20/0.49  % (28712)Success in time 0.135 s
%------------------------------------------------------------------------------
