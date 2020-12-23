%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:48 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :  295 (7902 expanded)
%              Number of clauses        :  217 (2382 expanded)
%              Number of leaves         :   22 (2215 expanded)
%              Depth                    :   34
%              Number of atoms          : 2329 (81940 expanded)
%              Number of equality atoms : 1253 (13033 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal clause size      :   24 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3)
        & ! [X3] :
            ( k1_funct_1(sK3,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK2))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    & ! [X3] :
        ( k1_funct_1(sK3,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f49,f48,f47])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ? [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6)
                              & r2_hidden(X6,u1_struct_0(X2))
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ? [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6)
                              & r2_hidden(X6,u1_struct_0(X2))
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X5,X4,X3,X2,X1] :
      ( ? [X6] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6)
          & r2_hidden(X6,u1_struct_0(X2))
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X2,X3,X4,X5))
        & r2_hidden(sK0(X1,X2,X3,X4,X5),u1_struct_0(X2))
        & m1_subset_1(sK0(X1,X2,X3,X4,X5),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X2,X3,X4,X5))
                            & r2_hidden(sK0(X1,X2,X3,X4,X5),u1_struct_0(X2))
                            & m1_subset_1(sK0(X1,X2,X3,X4,X5),u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f45])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
      | m1_subset_1(sK0(X1,X2,X3,X4,X5),u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
      | r2_hidden(sK0(X1,X2,X3,X4,X5),u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
      | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1993,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2572,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1993])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1996,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2569,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_18,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2001,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_52))
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2564,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_52)) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2011,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2554,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_3,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2014,plain,
    ( ~ r2_funct_2(X0_51,X1_51,X0_52,X1_52)
    | ~ v1_funct_2(X0_52,X0_51,X1_51)
    | ~ v1_funct_2(X1_52,X0_51,X1_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2551,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X0_51,X1_51,X1_52,X0_52) != iProver_top
    | v1_funct_2(X1_52,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_52,X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_4997,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = X1_52
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),X1_52,k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_2551])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2009,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2556,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2010,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2555,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_6978,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = X1_52
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),X1_52,k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4997,c_2556,c_2555])).

cnf(c_6982,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X2_50,X0_52) = X0_52
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2564,c_6978])).

cnf(c_8386,plain,
    ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_6982])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8483,plain,
    ( v2_pre_topc(X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8386,c_31,c_32,c_33,c_34,c_36,c_37])).

cnf(c_8484,plain,
    ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_8483])).

cnf(c_8494,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_8484])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8474,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8386])).

cnf(c_8541,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8494,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_8474])).

cnf(c_17,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0,X3,X4,X5),u1_struct_0(X3))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2002,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | m1_subset_1(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X3_50))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2563,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X3_50)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2002])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2000,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | m1_pre_topc(X2_50,X1_50)
    | ~ v2_pre_topc(X1_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2565,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_2881,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X3_50)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2563,c_2565])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2008,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2557,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_4087,plain,
    ( k4_tmap_1(X0_50,X1_50) = X0_52
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_2551])).

cnf(c_12,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2007,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ m1_pre_topc(X1_50,X0_50)
    | ~ v2_pre_topc(X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2059,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_5690,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
    | k4_tmap_1(X0_50,X1_50) = X0_52
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4087,c_2059])).

cnf(c_5691,plain,
    ( k4_tmap_1(X0_50,X1_50) = X0_52
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5690])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2006,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ v2_pre_topc(X1_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2559,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_5706,plain,
    ( k4_tmap_1(X0_50,X1_50) = X0_52
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5691,c_2559])).

cnf(c_6253,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X1_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X2_50)) = iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_50,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X3_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2881,c_5706])).

cnf(c_2558,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_22680,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X1_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X2_50)) = iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6253,c_2559,c_2557,c_2558])).

cnf(c_22686,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k4_tmap_1(sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_22680])).

cnf(c_22701,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22686,c_8541])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2019,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2036,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2015,plain,
    ( r2_funct_2(X0_51,X1_51,X0_52,X0_52)
    | ~ v1_funct_2(X0_52,X0_51,X1_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3035,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_2027,plain,
    ( ~ r2_funct_2(X0_51,X1_51,X0_52,X1_52)
    | r2_funct_2(X0_51,X1_51,X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_3131,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X0_52 != sK3
    | X1_52 != sK3 ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_3332,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | k4_tmap_1(sK1,sK2) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3131])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2013,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2552,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_3366,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_2552])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2005,plain,
    ( m1_pre_topc(X0_50,X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3845,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_3846,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3845])).

cnf(c_23908,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22701,c_31,c_32,c_33,c_34,c_35,c_25,c_36,c_24,c_37,c_23,c_38,c_21,c_2036,c_3035,c_3332,c_3366,c_3846])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2012,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
    | m1_subset_1(X0_52,u1_struct_0(X1_50))
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2553,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2012])).

cnf(c_23917,plain,
    ( m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_23908,c_2553])).

cnf(c_22979,plain,
    ( ~ m1_pre_topc(sK2,X0_50)
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50))
    | ~ m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_50) ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_22980,plain,
    ( m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22979])).

cnf(c_24569,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23917,c_31,c_32,c_33,c_34,c_35,c_25,c_36,c_24,c_37,c_23,c_38,c_21,c_2036,c_3035,c_3332,c_3366,c_3846,c_22701,c_22980])).

cnf(c_24570,plain,
    ( m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_24569])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1997,negated_conjecture,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
    | ~ r2_hidden(X0_52,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2568,plain,
    ( k1_funct_1(sK3,X0_52) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_24579,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24570,c_2568])).

cnf(c_8648,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_2881])).

cnf(c_9051,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8648,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3366,c_3846])).

cnf(c_9052,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_9051])).

cnf(c_9064,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_9052,c_2553])).

cnf(c_10434,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_50)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9064,c_34])).

cnf(c_10435,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_10434])).

cnf(c_10446,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_10435,c_2568])).

cnf(c_16,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | r2_hidden(sK0(X1,X0,X3,X4,X5),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2003,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | r2_hidden(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X0_50))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2562,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | r2_hidden(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X0_50)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_2843,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | r2_hidden(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X0_50)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2562,c_2565])).

cnf(c_8649,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_2843])).

cnf(c_9539,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8649,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3366,c_3846])).

cnf(c_9540,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_9539])).

cnf(c_10927,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10446,c_31,c_33,c_35,c_9540])).

cnf(c_10928,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_10927])).

cnf(c_10937,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_10928])).

cnf(c_5782,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_5783,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5782])).

cnf(c_3264,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_5807,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_5810,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5807])).

cnf(c_10990,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10937,c_31,c_32,c_33,c_35,c_5783,c_5810])).

cnf(c_10996,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10990,c_5706])).

cnf(c_25127,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24579,c_31,c_32,c_33,c_35,c_25,c_36,c_24,c_37,c_23,c_38,c_21,c_2036,c_3035,c_3332,c_10996])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2016,plain,
    ( ~ v1_funct_2(X0_52,X0_51,X1_51)
    | ~ m1_subset_1(X1_52,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_52)
    | v1_xboole_0(X0_51)
    | k3_funct_2(X0_51,X1_51,X0_52,X1_52) = k1_funct_1(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2549,plain,
    ( k3_funct_2(X0_51,X1_51,X0_52,X1_52) = k1_funct_1(X0_52,X1_52)
    | v1_funct_2(X0_52,X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_52,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_4996,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = k1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
    | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_2549])).

cnf(c_5830,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = k1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
    | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4996,c_2556,c_2555])).

cnf(c_5834,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_5830])).

cnf(c_5943,plain,
    ( v2_struct_0(X1_50) = iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5834,c_31,c_32,c_33,c_36,c_37])).

cnf(c_5944,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5943])).

cnf(c_6247,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k3_tmap_1(X4_50,X2_50,X0_50,X3_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X4_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2881,c_5944])).

cnf(c_2047,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_338,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_1988,plain,
    ( v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v1_xboole_0(u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_338])).

cnf(c_2090,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_7734,plain,
    ( v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,X4_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k3_tmap_1(X4_50,X2_50,X0_50,X3_50,X0_52),X1_52) = iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6247,c_2047,c_2090])).

cnf(c_7735,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k3_tmap_1(X4_50,X2_50,X0_50,X3_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X4_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7734])).

cnf(c_7763,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X2_50) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_7735])).

cnf(c_7856,plain,
    ( l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(sK2,X2_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52))
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7763,c_31,c_32,c_33,c_34,c_35])).

cnf(c_7857,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X2_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7856])).

cnf(c_7880,plain,
    ( k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52) = k4_tmap_1(X1_50,X2_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50)))
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_50,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X2_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7857,c_5706])).

cnf(c_8179,plain,
    ( k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52) = k4_tmap_1(X1_50,X2_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50)))
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7880,c_2559,c_2557,c_2558])).

cnf(c_8544,plain,
    ( k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52) = k4_tmap_1(X1_50,X2_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50))) = k1_funct_1(sK3,sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50)))
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8541,c_8179])).

cnf(c_12118,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_8544])).

cnf(c_12132,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12118,c_8541])).

cnf(c_8546,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(sK3,sK0(X0_50,X1_50,sK2,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X2_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8541,c_7857])).

cnf(c_9940,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_8546])).

cnf(c_10097,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9940,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3366,c_3846])).

cnf(c_10098,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_10097])).

cnf(c_10107,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_10098])).

cnf(c_10841,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10107,c_31,c_32,c_33,c_35,c_5783,c_5810])).

cnf(c_10847,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10841,c_5706])).

cnf(c_12185,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12132,c_31,c_32,c_33,c_35,c_25,c_36,c_24,c_37,c_23,c_38,c_21,c_2036,c_3035,c_3332,c_10847])).

cnf(c_25130,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_25127,c_12185])).

cnf(c_15,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X0,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X0,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2004,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | k3_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),X0_52,sK0(X1_50,X0_50,X3_50,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_50,X0_50,X3_50,X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2561,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_2919,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52),X1_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2561,c_2565])).

cnf(c_25552,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_25130,c_2919])).

cnf(c_10451,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_10435,c_2553])).

cnf(c_18925,plain,
    ( v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_50)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10451,c_2047])).

cnf(c_18926,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_18925])).

cnf(c_18939,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_18926])).

cnf(c_19015,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18939,c_31,c_33,c_34,c_3366,c_3846])).

cnf(c_19016,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_19015])).

cnf(c_6115,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X1_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_50,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | r2_hidden(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X3_50)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X3_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_5706])).

cnf(c_12384,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
    | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X1_50) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | r2_hidden(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X3_50)) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6115,c_2559,c_2557,c_2558])).

cnf(c_12389,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k4_tmap_1(sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_12384])).

cnf(c_12403,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12389,c_8541])).

cnf(c_13477,plain,
    ( r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12403,c_31,c_32,c_33,c_34,c_35,c_25,c_36,c_24,c_37,c_23,c_38,c_21,c_2036,c_3035,c_3332,c_3366,c_3846])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1999,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_52,u1_struct_0(X1_50))
    | ~ r2_hidden(X0_52,u1_struct_0(X0_50))
    | ~ v2_pre_topc(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2566,plain,
    ( k1_funct_1(k4_tmap_1(X0_50,X1_50),X0_52) = X0_52
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(X1_50)) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1999])).

cnf(c_13482,plain,
    ( k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_13477,c_2566])).

cnf(c_14167,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13482,c_34])).

cnf(c_14168,plain,
    ( k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_14167])).

cnf(c_19031,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19016,c_14168])).

cnf(c_12067,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_12068,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12067])).

cnf(c_3832,plain,
    ( ~ r2_funct_2(X0_51,X1_51,sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),X0_51,X1_51)
    | ~ v1_funct_2(sK3,X0_51,X1_51)
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_13501,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_3832])).

cnf(c_13502,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13501])).

cnf(c_14181,plain,
    ( k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10435,c_14168])).

cnf(c_14242,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14181])).

cnf(c_19743,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19031,c_31,c_32,c_33,c_35,c_25,c_36,c_24,c_37,c_23,c_38,c_21,c_2036,c_3035,c_3332,c_5783,c_5810,c_12068,c_13502,c_14242])).

cnf(c_25553,plain,
    ( sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25552,c_19743])).

cnf(c_25554,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_25553])).

cnf(c_25556,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25554])).

cnf(c_3373,plain,
    ( ~ r2_funct_2(X0_51,X1_51,k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_52)
    | ~ v1_funct_2(X0_52,X0_51,X1_51)
    | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51,X1_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3))
    | X0_52 = k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3) ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_4312,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3),k4_tmap_1(X1_50,X0_50))
    | ~ v1_funct_2(k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3),u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ v1_funct_1(k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3))
    | ~ v1_funct_1(k4_tmap_1(X1_50,X0_50))
    | k4_tmap_1(X1_50,X0_50) = k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3) ),
    inference(instantiation,[status(thm)],[c_3373])).

cnf(c_9032,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3) ),
    inference(instantiation,[status(thm)],[c_4312])).

cnf(c_24820,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_9032])).

cnf(c_24821,plain,
    ( k4_tmap_1(sK1,sK2) = k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24820])).

cnf(c_24823,plain,
    ( k4_tmap_1(sK1,sK2) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24821])).

cnf(c_2022,plain,
    ( ~ m1_subset_1(X0_52,X0_51)
    | m1_subset_1(X1_52,X0_51)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_3010,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X0_52 != sK3 ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_22997,plain,
    ( m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_22998,plain,
    ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != sK3
    | m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22997])).

cnf(c_23000,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) != sK3
    | m1_subset_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22998])).

cnf(c_3170,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
    | X1_52 != k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)
    | X0_52 != sK3 ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_22326,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) != k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3170])).

cnf(c_22331,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK1,sK1,sK2,sK2,sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) != k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_22326])).

cnf(c_2026,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_12006,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
    | k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != X0_52 ),
    inference(instantiation,[status(thm)],[c_2026])).

cnf(c_12007,plain,
    ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != X0_52
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12006])).

cnf(c_12009,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) != sK3
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12007])).

cnf(c_3077,plain,
    ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),u1_struct_0(X1_50),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_5591,plain,
    ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3077])).

cnf(c_5596,plain,
    ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5591])).

cnf(c_5598,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5596])).

cnf(c_3067,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_3069,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK1,sK1,sK2,sK2,sK3))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3067])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25556,c_24823,c_23000,c_22331,c_13501,c_12068,c_12067,c_12009,c_8474,c_5810,c_5807,c_5783,c_5782,c_5598,c_3846,c_3366,c_3332,c_3069,c_3035,c_2036,c_21,c_38,c_23,c_37,c_24,c_36,c_25,c_35,c_26,c_34,c_27,c_33,c_28,c_32,c_29,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:05:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.49/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/2.00  
% 11.49/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.49/2.00  
% 11.49/2.00  ------  iProver source info
% 11.49/2.00  
% 11.49/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.49/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.49/2.00  git: non_committed_changes: false
% 11.49/2.00  git: last_make_outside_of_git: false
% 11.49/2.00  
% 11.49/2.00  ------ 
% 11.49/2.00  
% 11.49/2.00  ------ Input Options
% 11.49/2.00  
% 11.49/2.00  --out_options                           all
% 11.49/2.00  --tptp_safe_out                         true
% 11.49/2.00  --problem_path                          ""
% 11.49/2.00  --include_path                          ""
% 11.49/2.00  --clausifier                            res/vclausify_rel
% 11.49/2.00  --clausifier_options                    --mode clausify
% 11.49/2.00  --stdin                                 false
% 11.49/2.00  --stats_out                             all
% 11.49/2.00  
% 11.49/2.00  ------ General Options
% 11.49/2.00  
% 11.49/2.00  --fof                                   false
% 11.49/2.00  --time_out_real                         305.
% 11.49/2.00  --time_out_virtual                      -1.
% 11.49/2.00  --symbol_type_check                     false
% 11.49/2.00  --clausify_out                          false
% 11.49/2.00  --sig_cnt_out                           false
% 11.49/2.00  --trig_cnt_out                          false
% 11.49/2.00  --trig_cnt_out_tolerance                1.
% 11.49/2.00  --trig_cnt_out_sk_spl                   false
% 11.49/2.00  --abstr_cl_out                          false
% 11.49/2.00  
% 11.49/2.00  ------ Global Options
% 11.49/2.00  
% 11.49/2.00  --schedule                              default
% 11.49/2.00  --add_important_lit                     false
% 11.49/2.00  --prop_solver_per_cl                    1000
% 11.49/2.00  --min_unsat_core                        false
% 11.49/2.00  --soft_assumptions                      false
% 11.49/2.00  --soft_lemma_size                       3
% 11.49/2.00  --prop_impl_unit_size                   0
% 11.49/2.00  --prop_impl_unit                        []
% 11.49/2.00  --share_sel_clauses                     true
% 11.49/2.00  --reset_solvers                         false
% 11.49/2.00  --bc_imp_inh                            [conj_cone]
% 11.49/2.00  --conj_cone_tolerance                   3.
% 11.49/2.00  --extra_neg_conj                        none
% 11.49/2.00  --large_theory_mode                     true
% 11.49/2.00  --prolific_symb_bound                   200
% 11.49/2.00  --lt_threshold                          2000
% 11.49/2.00  --clause_weak_htbl                      true
% 11.49/2.00  --gc_record_bc_elim                     false
% 11.49/2.00  
% 11.49/2.00  ------ Preprocessing Options
% 11.49/2.00  
% 11.49/2.00  --preprocessing_flag                    true
% 11.49/2.00  --time_out_prep_mult                    0.1
% 11.49/2.00  --splitting_mode                        input
% 11.49/2.00  --splitting_grd                         true
% 11.49/2.00  --splitting_cvd                         false
% 11.49/2.00  --splitting_cvd_svl                     false
% 11.49/2.00  --splitting_nvd                         32
% 11.49/2.00  --sub_typing                            true
% 11.49/2.00  --prep_gs_sim                           true
% 11.49/2.00  --prep_unflatten                        true
% 11.49/2.00  --prep_res_sim                          true
% 11.49/2.00  --prep_upred                            true
% 11.49/2.00  --prep_sem_filter                       exhaustive
% 11.49/2.00  --prep_sem_filter_out                   false
% 11.49/2.00  --pred_elim                             true
% 11.49/2.00  --res_sim_input                         true
% 11.49/2.00  --eq_ax_congr_red                       true
% 11.49/2.00  --pure_diseq_elim                       true
% 11.49/2.00  --brand_transform                       false
% 11.49/2.00  --non_eq_to_eq                          false
% 11.49/2.00  --prep_def_merge                        true
% 11.49/2.00  --prep_def_merge_prop_impl              false
% 11.49/2.00  --prep_def_merge_mbd                    true
% 11.49/2.00  --prep_def_merge_tr_red                 false
% 11.49/2.00  --prep_def_merge_tr_cl                  false
% 11.49/2.00  --smt_preprocessing                     true
% 11.49/2.00  --smt_ac_axioms                         fast
% 11.49/2.00  --preprocessed_out                      false
% 11.49/2.00  --preprocessed_stats                    false
% 11.49/2.00  
% 11.49/2.00  ------ Abstraction refinement Options
% 11.49/2.00  
% 11.49/2.00  --abstr_ref                             []
% 11.49/2.00  --abstr_ref_prep                        false
% 11.49/2.00  --abstr_ref_until_sat                   false
% 11.49/2.00  --abstr_ref_sig_restrict                funpre
% 11.49/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.49/2.00  --abstr_ref_under                       []
% 11.49/2.00  
% 11.49/2.00  ------ SAT Options
% 11.49/2.00  
% 11.49/2.00  --sat_mode                              false
% 11.49/2.00  --sat_fm_restart_options                ""
% 11.49/2.00  --sat_gr_def                            false
% 11.49/2.00  --sat_epr_types                         true
% 11.49/2.00  --sat_non_cyclic_types                  false
% 11.49/2.00  --sat_finite_models                     false
% 11.49/2.00  --sat_fm_lemmas                         false
% 11.49/2.00  --sat_fm_prep                           false
% 11.49/2.00  --sat_fm_uc_incr                        true
% 11.49/2.00  --sat_out_model                         small
% 11.49/2.00  --sat_out_clauses                       false
% 11.49/2.00  
% 11.49/2.00  ------ QBF Options
% 11.49/2.00  
% 11.49/2.00  --qbf_mode                              false
% 11.49/2.00  --qbf_elim_univ                         false
% 11.49/2.00  --qbf_dom_inst                          none
% 11.49/2.00  --qbf_dom_pre_inst                      false
% 11.49/2.00  --qbf_sk_in                             false
% 11.49/2.00  --qbf_pred_elim                         true
% 11.49/2.00  --qbf_split                             512
% 11.49/2.00  
% 11.49/2.00  ------ BMC1 Options
% 11.49/2.00  
% 11.49/2.00  --bmc1_incremental                      false
% 11.49/2.00  --bmc1_axioms                           reachable_all
% 11.49/2.00  --bmc1_min_bound                        0
% 11.49/2.00  --bmc1_max_bound                        -1
% 11.49/2.00  --bmc1_max_bound_default                -1
% 11.49/2.00  --bmc1_symbol_reachability              true
% 11.49/2.00  --bmc1_property_lemmas                  false
% 11.49/2.00  --bmc1_k_induction                      false
% 11.49/2.00  --bmc1_non_equiv_states                 false
% 11.49/2.00  --bmc1_deadlock                         false
% 11.49/2.00  --bmc1_ucm                              false
% 11.49/2.00  --bmc1_add_unsat_core                   none
% 11.49/2.00  --bmc1_unsat_core_children              false
% 11.49/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.49/2.00  --bmc1_out_stat                         full
% 11.49/2.00  --bmc1_ground_init                      false
% 11.49/2.00  --bmc1_pre_inst_next_state              false
% 11.49/2.00  --bmc1_pre_inst_state                   false
% 11.49/2.00  --bmc1_pre_inst_reach_state             false
% 11.49/2.00  --bmc1_out_unsat_core                   false
% 11.49/2.00  --bmc1_aig_witness_out                  false
% 11.49/2.00  --bmc1_verbose                          false
% 11.49/2.00  --bmc1_dump_clauses_tptp                false
% 11.49/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.49/2.00  --bmc1_dump_file                        -
% 11.49/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.49/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.49/2.00  --bmc1_ucm_extend_mode                  1
% 11.49/2.00  --bmc1_ucm_init_mode                    2
% 11.49/2.00  --bmc1_ucm_cone_mode                    none
% 11.49/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.49/2.00  --bmc1_ucm_relax_model                  4
% 11.49/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.49/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.49/2.00  --bmc1_ucm_layered_model                none
% 11.49/2.00  --bmc1_ucm_max_lemma_size               10
% 11.49/2.00  
% 11.49/2.00  ------ AIG Options
% 11.49/2.00  
% 11.49/2.00  --aig_mode                              false
% 11.49/2.00  
% 11.49/2.00  ------ Instantiation Options
% 11.49/2.00  
% 11.49/2.00  --instantiation_flag                    true
% 11.49/2.00  --inst_sos_flag                         false
% 11.49/2.00  --inst_sos_phase                        true
% 11.49/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.49/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.49/2.00  --inst_lit_sel_side                     num_symb
% 11.49/2.00  --inst_solver_per_active                1400
% 11.49/2.00  --inst_solver_calls_frac                1.
% 11.49/2.00  --inst_passive_queue_type               priority_queues
% 11.49/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.49/2.00  --inst_passive_queues_freq              [25;2]
% 11.49/2.00  --inst_dismatching                      true
% 11.49/2.00  --inst_eager_unprocessed_to_passive     true
% 11.49/2.00  --inst_prop_sim_given                   true
% 11.49/2.00  --inst_prop_sim_new                     false
% 11.49/2.00  --inst_subs_new                         false
% 11.49/2.00  --inst_eq_res_simp                      false
% 11.49/2.00  --inst_subs_given                       false
% 11.49/2.00  --inst_orphan_elimination               true
% 11.49/2.00  --inst_learning_loop_flag               true
% 11.49/2.00  --inst_learning_start                   3000
% 11.49/2.00  --inst_learning_factor                  2
% 11.49/2.00  --inst_start_prop_sim_after_learn       3
% 11.49/2.00  --inst_sel_renew                        solver
% 11.49/2.00  --inst_lit_activity_flag                true
% 11.49/2.00  --inst_restr_to_given                   false
% 11.49/2.00  --inst_activity_threshold               500
% 11.49/2.00  --inst_out_proof                        true
% 11.49/2.00  
% 11.49/2.00  ------ Resolution Options
% 11.49/2.00  
% 11.49/2.00  --resolution_flag                       true
% 11.49/2.00  --res_lit_sel                           adaptive
% 11.49/2.00  --res_lit_sel_side                      none
% 11.49/2.00  --res_ordering                          kbo
% 11.49/2.00  --res_to_prop_solver                    active
% 11.49/2.00  --res_prop_simpl_new                    false
% 11.49/2.00  --res_prop_simpl_given                  true
% 11.49/2.00  --res_passive_queue_type                priority_queues
% 11.49/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.49/2.00  --res_passive_queues_freq               [15;5]
% 11.49/2.00  --res_forward_subs                      full
% 11.49/2.00  --res_backward_subs                     full
% 11.49/2.00  --res_forward_subs_resolution           true
% 11.49/2.00  --res_backward_subs_resolution          true
% 11.49/2.00  --res_orphan_elimination                true
% 11.49/2.00  --res_time_limit                        2.
% 11.49/2.00  --res_out_proof                         true
% 11.49/2.00  
% 11.49/2.00  ------ Superposition Options
% 11.49/2.00  
% 11.49/2.00  --superposition_flag                    true
% 11.49/2.00  --sup_passive_queue_type                priority_queues
% 11.49/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.49/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.49/2.00  --demod_completeness_check              fast
% 11.49/2.00  --demod_use_ground                      true
% 11.49/2.00  --sup_to_prop_solver                    passive
% 11.49/2.00  --sup_prop_simpl_new                    true
% 11.49/2.00  --sup_prop_simpl_given                  true
% 11.49/2.00  --sup_fun_splitting                     false
% 11.49/2.00  --sup_smt_interval                      50000
% 11.49/2.00  
% 11.49/2.00  ------ Superposition Simplification Setup
% 11.49/2.00  
% 11.49/2.00  --sup_indices_passive                   []
% 11.49/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.49/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.49/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.49/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.49/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.49/2.00  --sup_full_bw                           [BwDemod]
% 11.49/2.00  --sup_immed_triv                        [TrivRules]
% 11.49/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.49/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.49/2.00  --sup_immed_bw_main                     []
% 11.49/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.49/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.49/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.49/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.49/2.00  
% 11.49/2.00  ------ Combination Options
% 11.49/2.00  
% 11.49/2.00  --comb_res_mult                         3
% 11.49/2.00  --comb_sup_mult                         2
% 11.49/2.00  --comb_inst_mult                        10
% 11.49/2.00  
% 11.49/2.00  ------ Debug Options
% 11.49/2.00  
% 11.49/2.00  --dbg_backtrace                         false
% 11.49/2.00  --dbg_dump_prop_clauses                 false
% 11.49/2.00  --dbg_dump_prop_clauses_file            -
% 11.49/2.00  --dbg_out_stat                          false
% 11.49/2.00  ------ Parsing...
% 11.49/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.49/2.00  
% 11.49/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.49/2.00  
% 11.49/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.49/2.00  
% 11.49/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.49/2.00  ------ Proving...
% 11.49/2.00  ------ Problem Properties 
% 11.49/2.00  
% 11.49/2.00  
% 11.49/2.00  clauses                                 30
% 11.49/2.00  conjectures                             10
% 11.49/2.00  EPR                                     10
% 11.49/2.00  Horn                                    16
% 11.49/2.00  unary                                   9
% 11.49/2.00  binary                                  1
% 11.49/2.00  lits                                    180
% 11.49/2.00  lits eq                                 5
% 11.49/2.00  fd_pure                                 0
% 11.49/2.00  fd_pseudo                               0
% 11.49/2.00  fd_cond                                 0
% 11.49/2.00  fd_pseudo_cond                          1
% 11.49/2.00  AC symbols                              0
% 11.49/2.00  
% 11.49/2.00  ------ Schedule dynamic 5 is on 
% 11.49/2.00  
% 11.49/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.49/2.00  
% 11.49/2.00  
% 11.49/2.00  ------ 
% 11.49/2.00  Current options:
% 11.49/2.00  ------ 
% 11.49/2.00  
% 11.49/2.00  ------ Input Options
% 11.49/2.00  
% 11.49/2.00  --out_options                           all
% 11.49/2.00  --tptp_safe_out                         true
% 11.49/2.00  --problem_path                          ""
% 11.49/2.00  --include_path                          ""
% 11.49/2.00  --clausifier                            res/vclausify_rel
% 11.49/2.00  --clausifier_options                    --mode clausify
% 11.49/2.00  --stdin                                 false
% 11.49/2.00  --stats_out                             all
% 11.49/2.00  
% 11.49/2.00  ------ General Options
% 11.49/2.00  
% 11.49/2.00  --fof                                   false
% 11.49/2.00  --time_out_real                         305.
% 11.49/2.00  --time_out_virtual                      -1.
% 11.49/2.00  --symbol_type_check                     false
% 11.49/2.00  --clausify_out                          false
% 11.49/2.00  --sig_cnt_out                           false
% 11.49/2.00  --trig_cnt_out                          false
% 11.49/2.00  --trig_cnt_out_tolerance                1.
% 11.49/2.00  --trig_cnt_out_sk_spl                   false
% 11.49/2.00  --abstr_cl_out                          false
% 11.49/2.00  
% 11.49/2.00  ------ Global Options
% 11.49/2.00  
% 11.49/2.00  --schedule                              default
% 11.49/2.00  --add_important_lit                     false
% 11.49/2.00  --prop_solver_per_cl                    1000
% 11.49/2.00  --min_unsat_core                        false
% 11.49/2.00  --soft_assumptions                      false
% 11.49/2.00  --soft_lemma_size                       3
% 11.49/2.00  --prop_impl_unit_size                   0
% 11.49/2.00  --prop_impl_unit                        []
% 11.49/2.00  --share_sel_clauses                     true
% 11.49/2.00  --reset_solvers                         false
% 11.49/2.00  --bc_imp_inh                            [conj_cone]
% 11.49/2.00  --conj_cone_tolerance                   3.
% 11.49/2.00  --extra_neg_conj                        none
% 11.49/2.00  --large_theory_mode                     true
% 11.49/2.00  --prolific_symb_bound                   200
% 11.49/2.00  --lt_threshold                          2000
% 11.49/2.00  --clause_weak_htbl                      true
% 11.49/2.00  --gc_record_bc_elim                     false
% 11.49/2.00  
% 11.49/2.00  ------ Preprocessing Options
% 11.49/2.00  
% 11.49/2.00  --preprocessing_flag                    true
% 11.49/2.00  --time_out_prep_mult                    0.1
% 11.49/2.00  --splitting_mode                        input
% 11.49/2.00  --splitting_grd                         true
% 11.49/2.00  --splitting_cvd                         false
% 11.49/2.00  --splitting_cvd_svl                     false
% 11.49/2.00  --splitting_nvd                         32
% 11.49/2.00  --sub_typing                            true
% 11.49/2.00  --prep_gs_sim                           true
% 11.49/2.00  --prep_unflatten                        true
% 11.49/2.00  --prep_res_sim                          true
% 11.49/2.00  --prep_upred                            true
% 11.49/2.00  --prep_sem_filter                       exhaustive
% 11.49/2.00  --prep_sem_filter_out                   false
% 11.49/2.00  --pred_elim                             true
% 11.49/2.00  --res_sim_input                         true
% 11.49/2.00  --eq_ax_congr_red                       true
% 11.49/2.00  --pure_diseq_elim                       true
% 11.49/2.00  --brand_transform                       false
% 11.49/2.00  --non_eq_to_eq                          false
% 11.49/2.00  --prep_def_merge                        true
% 11.49/2.00  --prep_def_merge_prop_impl              false
% 11.49/2.00  --prep_def_merge_mbd                    true
% 11.49/2.00  --prep_def_merge_tr_red                 false
% 11.49/2.00  --prep_def_merge_tr_cl                  false
% 11.49/2.00  --smt_preprocessing                     true
% 11.49/2.00  --smt_ac_axioms                         fast
% 11.49/2.00  --preprocessed_out                      false
% 11.49/2.00  --preprocessed_stats                    false
% 11.49/2.00  
% 11.49/2.00  ------ Abstraction refinement Options
% 11.49/2.00  
% 11.49/2.00  --abstr_ref                             []
% 11.49/2.00  --abstr_ref_prep                        false
% 11.49/2.00  --abstr_ref_until_sat                   false
% 11.49/2.00  --abstr_ref_sig_restrict                funpre
% 11.49/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.49/2.00  --abstr_ref_under                       []
% 11.49/2.00  
% 11.49/2.00  ------ SAT Options
% 11.49/2.00  
% 11.49/2.00  --sat_mode                              false
% 11.49/2.00  --sat_fm_restart_options                ""
% 11.49/2.00  --sat_gr_def                            false
% 11.49/2.00  --sat_epr_types                         true
% 11.49/2.00  --sat_non_cyclic_types                  false
% 11.49/2.00  --sat_finite_models                     false
% 11.49/2.00  --sat_fm_lemmas                         false
% 11.49/2.00  --sat_fm_prep                           false
% 11.49/2.00  --sat_fm_uc_incr                        true
% 11.49/2.00  --sat_out_model                         small
% 11.49/2.00  --sat_out_clauses                       false
% 11.49/2.00  
% 11.49/2.00  ------ QBF Options
% 11.49/2.00  
% 11.49/2.00  --qbf_mode                              false
% 11.49/2.00  --qbf_elim_univ                         false
% 11.49/2.00  --qbf_dom_inst                          none
% 11.49/2.00  --qbf_dom_pre_inst                      false
% 11.49/2.00  --qbf_sk_in                             false
% 11.49/2.00  --qbf_pred_elim                         true
% 11.49/2.00  --qbf_split                             512
% 11.49/2.00  
% 11.49/2.00  ------ BMC1 Options
% 11.49/2.00  
% 11.49/2.00  --bmc1_incremental                      false
% 11.49/2.00  --bmc1_axioms                           reachable_all
% 11.49/2.00  --bmc1_min_bound                        0
% 11.49/2.00  --bmc1_max_bound                        -1
% 11.49/2.00  --bmc1_max_bound_default                -1
% 11.49/2.00  --bmc1_symbol_reachability              true
% 11.49/2.00  --bmc1_property_lemmas                  false
% 11.49/2.00  --bmc1_k_induction                      false
% 11.49/2.00  --bmc1_non_equiv_states                 false
% 11.49/2.00  --bmc1_deadlock                         false
% 11.49/2.00  --bmc1_ucm                              false
% 11.49/2.00  --bmc1_add_unsat_core                   none
% 11.49/2.00  --bmc1_unsat_core_children              false
% 11.49/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.49/2.00  --bmc1_out_stat                         full
% 11.49/2.00  --bmc1_ground_init                      false
% 11.49/2.00  --bmc1_pre_inst_next_state              false
% 11.49/2.00  --bmc1_pre_inst_state                   false
% 11.49/2.00  --bmc1_pre_inst_reach_state             false
% 11.49/2.00  --bmc1_out_unsat_core                   false
% 11.49/2.00  --bmc1_aig_witness_out                  false
% 11.49/2.00  --bmc1_verbose                          false
% 11.49/2.00  --bmc1_dump_clauses_tptp                false
% 11.49/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.49/2.00  --bmc1_dump_file                        -
% 11.49/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.49/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.49/2.00  --bmc1_ucm_extend_mode                  1
% 11.49/2.00  --bmc1_ucm_init_mode                    2
% 11.49/2.00  --bmc1_ucm_cone_mode                    none
% 11.49/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.49/2.00  --bmc1_ucm_relax_model                  4
% 11.49/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.49/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.49/2.00  --bmc1_ucm_layered_model                none
% 11.49/2.00  --bmc1_ucm_max_lemma_size               10
% 11.49/2.00  
% 11.49/2.00  ------ AIG Options
% 11.49/2.00  
% 11.49/2.00  --aig_mode                              false
% 11.49/2.00  
% 11.49/2.00  ------ Instantiation Options
% 11.49/2.00  
% 11.49/2.00  --instantiation_flag                    true
% 11.49/2.00  --inst_sos_flag                         false
% 11.49/2.00  --inst_sos_phase                        true
% 11.49/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.49/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.49/2.00  --inst_lit_sel_side                     none
% 11.49/2.00  --inst_solver_per_active                1400
% 11.49/2.00  --inst_solver_calls_frac                1.
% 11.49/2.00  --inst_passive_queue_type               priority_queues
% 11.49/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.49/2.00  --inst_passive_queues_freq              [25;2]
% 11.49/2.00  --inst_dismatching                      true
% 11.49/2.00  --inst_eager_unprocessed_to_passive     true
% 11.49/2.00  --inst_prop_sim_given                   true
% 11.49/2.00  --inst_prop_sim_new                     false
% 11.49/2.00  --inst_subs_new                         false
% 11.49/2.00  --inst_eq_res_simp                      false
% 11.49/2.00  --inst_subs_given                       false
% 11.49/2.00  --inst_orphan_elimination               true
% 11.49/2.00  --inst_learning_loop_flag               true
% 11.49/2.00  --inst_learning_start                   3000
% 11.49/2.00  --inst_learning_factor                  2
% 11.49/2.00  --inst_start_prop_sim_after_learn       3
% 11.49/2.00  --inst_sel_renew                        solver
% 11.49/2.00  --inst_lit_activity_flag                true
% 11.49/2.00  --inst_restr_to_given                   false
% 11.49/2.00  --inst_activity_threshold               500
% 11.49/2.00  --inst_out_proof                        true
% 11.49/2.00  
% 11.49/2.00  ------ Resolution Options
% 11.49/2.00  
% 11.49/2.00  --resolution_flag                       false
% 11.49/2.00  --res_lit_sel                           adaptive
% 11.49/2.00  --res_lit_sel_side                      none
% 11.49/2.00  --res_ordering                          kbo
% 11.49/2.00  --res_to_prop_solver                    active
% 11.49/2.00  --res_prop_simpl_new                    false
% 11.49/2.00  --res_prop_simpl_given                  true
% 11.49/2.00  --res_passive_queue_type                priority_queues
% 11.49/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.49/2.00  --res_passive_queues_freq               [15;5]
% 11.49/2.00  --res_forward_subs                      full
% 11.49/2.00  --res_backward_subs                     full
% 11.49/2.00  --res_forward_subs_resolution           true
% 11.49/2.00  --res_backward_subs_resolution          true
% 11.49/2.00  --res_orphan_elimination                true
% 11.49/2.00  --res_time_limit                        2.
% 11.49/2.00  --res_out_proof                         true
% 11.49/2.00  
% 11.49/2.00  ------ Superposition Options
% 11.49/2.00  
% 11.49/2.00  --superposition_flag                    true
% 11.49/2.00  --sup_passive_queue_type                priority_queues
% 11.49/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.49/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.49/2.00  --demod_completeness_check              fast
% 11.49/2.00  --demod_use_ground                      true
% 11.49/2.00  --sup_to_prop_solver                    passive
% 11.49/2.00  --sup_prop_simpl_new                    true
% 11.49/2.00  --sup_prop_simpl_given                  true
% 11.49/2.00  --sup_fun_splitting                     false
% 11.49/2.00  --sup_smt_interval                      50000
% 11.49/2.00  
% 11.49/2.00  ------ Superposition Simplification Setup
% 11.49/2.00  
% 11.49/2.00  --sup_indices_passive                   []
% 11.49/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.49/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.49/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.49/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.49/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.49/2.00  --sup_full_bw                           [BwDemod]
% 11.49/2.00  --sup_immed_triv                        [TrivRules]
% 11.49/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.49/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.49/2.00  --sup_immed_bw_main                     []
% 11.49/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.49/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.49/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.49/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.49/2.00  
% 11.49/2.00  ------ Combination Options
% 11.49/2.00  
% 11.49/2.00  --comb_res_mult                         3
% 11.49/2.00  --comb_sup_mult                         2
% 11.49/2.00  --comb_inst_mult                        10
% 11.49/2.00  
% 11.49/2.00  ------ Debug Options
% 11.49/2.00  
% 11.49/2.00  --dbg_backtrace                         false
% 11.49/2.00  --dbg_dump_prop_clauses                 false
% 11.49/2.00  --dbg_dump_prop_clauses_file            -
% 11.49/2.00  --dbg_out_stat                          false
% 11.49/2.00  
% 11.49/2.00  
% 11.49/2.00  
% 11.49/2.00  
% 11.49/2.00  ------ Proving...
% 11.49/2.00  
% 11.49/2.00  
% 11.49/2.00  % SZS status Theorem for theBenchmark.p
% 11.49/2.00  
% 11.49/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.49/2.00  
% 11.49/2.00  fof(f15,conjecture,(
% 11.49/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f16,negated_conjecture,(
% 11.49/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 11.49/2.00    inference(negated_conjecture,[],[f15])).
% 11.49/2.00  
% 11.49/2.00  fof(f42,plain,(
% 11.49/2.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f16])).
% 11.49/2.00  
% 11.49/2.00  fof(f43,plain,(
% 11.49/2.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f42])).
% 11.49/2.00  
% 11.49/2.00  fof(f49,plain,(
% 11.49/2.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 11.49/2.00    introduced(choice_axiom,[])).
% 11.49/2.00  
% 11.49/2.00  fof(f48,plain,(
% 11.49/2.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 11.49/2.00    introduced(choice_axiom,[])).
% 11.49/2.00  
% 11.49/2.00  fof(f47,plain,(
% 11.49/2.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 11.49/2.00    introduced(choice_axiom,[])).
% 11.49/2.00  
% 11.49/2.00  fof(f50,plain,(
% 11.49/2.00    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 11.49/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f49,f48,f47])).
% 11.49/2.00  
% 11.49/2.00  fof(f76,plain,(
% 11.49/2.00    m1_pre_topc(sK2,sK1)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f79,plain,(
% 11.49/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f12,axiom,(
% 11.49/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f36,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f12])).
% 11.49/2.00  
% 11.49/2.00  fof(f37,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f36])).
% 11.49/2.00  
% 11.49/2.00  fof(f69,plain,(
% 11.49/2.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f37])).
% 11.49/2.00  
% 11.49/2.00  fof(f8,axiom,(
% 11.49/2.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f29,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f8])).
% 11.49/2.00  
% 11.49/2.00  fof(f30,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f29])).
% 11.49/2.00  
% 11.49/2.00  fof(f61,plain,(
% 11.49/2.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f30])).
% 11.49/2.00  
% 11.49/2.00  fof(f3,axiom,(
% 11.49/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f21,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.49/2.00    inference(ennf_transformation,[],[f3])).
% 11.49/2.00  
% 11.49/2.00  fof(f22,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.49/2.00    inference(flattening,[],[f21])).
% 11.49/2.00  
% 11.49/2.00  fof(f44,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.49/2.00    inference(nnf_transformation,[],[f22])).
% 11.49/2.00  
% 11.49/2.00  fof(f53,plain,(
% 11.49/2.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f44])).
% 11.49/2.00  
% 11.49/2.00  fof(f59,plain,(
% 11.49/2.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f30])).
% 11.49/2.00  
% 11.49/2.00  fof(f60,plain,(
% 11.49/2.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f30])).
% 11.49/2.00  
% 11.49/2.00  fof(f72,plain,(
% 11.49/2.00    ~v2_struct_0(sK1)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f73,plain,(
% 11.49/2.00    v2_pre_topc(sK1)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f74,plain,(
% 11.49/2.00    l1_pre_topc(sK1)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f75,plain,(
% 11.49/2.00    ~v2_struct_0(sK2)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f77,plain,(
% 11.49/2.00    v1_funct_1(sK3)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f78,plain,(
% 11.49/2.00    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f11,axiom,(
% 11.49/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f34,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | ? [X6] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6) & r2_hidden(X6,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f11])).
% 11.49/2.00  
% 11.49/2.00  fof(f35,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | ? [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6) & r2_hidden(X6,u1_struct_0(X2)) & m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f34])).
% 11.49/2.00  
% 11.49/2.00  fof(f45,plain,(
% 11.49/2.00    ! [X5,X4,X3,X2,X1] : (? [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6) & r2_hidden(X6,u1_struct_0(X2)) & m1_subset_1(X6,u1_struct_0(X3))) => (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X2,X3,X4,X5)) & r2_hidden(sK0(X1,X2,X3,X4,X5),u1_struct_0(X2)) & m1_subset_1(sK0(X1,X2,X3,X4,X5),u1_struct_0(X3))))),
% 11.49/2.00    introduced(choice_axiom,[])).
% 11.49/2.00  
% 11.49/2.00  fof(f46,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X2,X3,X4,X5)) & r2_hidden(sK0(X1,X2,X3,X4,X5),u1_struct_0(X2)) & m1_subset_1(sK0(X1,X2,X3,X4,X5),u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f45])).
% 11.49/2.00  
% 11.49/2.00  fof(f66,plain,(
% 11.49/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | m1_subset_1(sK0(X1,X2,X3,X4,X5),u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f46])).
% 11.49/2.00  
% 11.49/2.00  fof(f13,axiom,(
% 11.49/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f38,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f13])).
% 11.49/2.00  
% 11.49/2.00  fof(f39,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.49/2.00    inference(flattening,[],[f38])).
% 11.49/2.00  
% 11.49/2.00  fof(f70,plain,(
% 11.49/2.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f39])).
% 11.49/2.00  
% 11.49/2.00  fof(f9,axiom,(
% 11.49/2.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f31,plain,(
% 11.49/2.00    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f9])).
% 11.49/2.00  
% 11.49/2.00  fof(f32,plain,(
% 11.49/2.00    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f31])).
% 11.49/2.00  
% 11.49/2.00  fof(f64,plain,(
% 11.49/2.00    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f32])).
% 11.49/2.00  
% 11.49/2.00  fof(f63,plain,(
% 11.49/2.00    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f32])).
% 11.49/2.00  
% 11.49/2.00  fof(f62,plain,(
% 11.49/2.00    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f32])).
% 11.49/2.00  
% 11.49/2.00  fof(f81,plain,(
% 11.49/2.00    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f54,plain,(
% 11.49/2.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f44])).
% 11.49/2.00  
% 11.49/2.00  fof(f82,plain,(
% 11.49/2.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.49/2.00    inference(equality_resolution,[],[f54])).
% 11.49/2.00  
% 11.49/2.00  fof(f5,axiom,(
% 11.49/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f24,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.49/2.00    inference(ennf_transformation,[],[f5])).
% 11.49/2.00  
% 11.49/2.00  fof(f56,plain,(
% 11.49/2.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f24])).
% 11.49/2.00  
% 11.49/2.00  fof(f10,axiom,(
% 11.49/2.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f33,plain,(
% 11.49/2.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.49/2.00    inference(ennf_transformation,[],[f10])).
% 11.49/2.00  
% 11.49/2.00  fof(f65,plain,(
% 11.49/2.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f33])).
% 11.49/2.00  
% 11.49/2.00  fof(f7,axiom,(
% 11.49/2.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f27,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f7])).
% 11.49/2.00  
% 11.49/2.00  fof(f28,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f27])).
% 11.49/2.00  
% 11.49/2.00  fof(f58,plain,(
% 11.49/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f28])).
% 11.49/2.00  
% 11.49/2.00  fof(f80,plain,(
% 11.49/2.00    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 11.49/2.00    inference(cnf_transformation,[],[f50])).
% 11.49/2.00  
% 11.49/2.00  fof(f67,plain,(
% 11.49/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | r2_hidden(sK0(X1,X2,X3,X4,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f46])).
% 11.49/2.00  
% 11.49/2.00  fof(f2,axiom,(
% 11.49/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f19,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f2])).
% 11.49/2.00  
% 11.49/2.00  fof(f20,plain,(
% 11.49/2.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 11.49/2.00    inference(flattening,[],[f19])).
% 11.49/2.00  
% 11.49/2.00  fof(f52,plain,(
% 11.49/2.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f20])).
% 11.49/2.00  
% 11.49/2.00  fof(f4,axiom,(
% 11.49/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f23,plain,(
% 11.49/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.49/2.00    inference(ennf_transformation,[],[f4])).
% 11.49/2.00  
% 11.49/2.00  fof(f55,plain,(
% 11.49/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f23])).
% 11.49/2.00  
% 11.49/2.00  fof(f6,axiom,(
% 11.49/2.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f25,plain,(
% 11.49/2.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f6])).
% 11.49/2.00  
% 11.49/2.00  fof(f26,plain,(
% 11.49/2.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f25])).
% 11.49/2.00  
% 11.49/2.00  fof(f57,plain,(
% 11.49/2.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f26])).
% 11.49/2.00  
% 11.49/2.00  fof(f68,plain,(
% 11.49/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f46])).
% 11.49/2.00  
% 11.49/2.00  fof(f14,axiom,(
% 11.49/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 11.49/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.00  
% 11.49/2.00  fof(f40,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.49/2.00    inference(ennf_transformation,[],[f14])).
% 11.49/2.00  
% 11.49/2.00  fof(f41,plain,(
% 11.49/2.00    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.49/2.00    inference(flattening,[],[f40])).
% 11.49/2.00  
% 11.49/2.00  fof(f71,plain,(
% 11.49/2.00    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.49/2.00    inference(cnf_transformation,[],[f41])).
% 11.49/2.00  
% 11.49/2.00  cnf(c_26,negated_conjecture,
% 11.49/2.00      ( m1_pre_topc(sK2,sK1) ),
% 11.49/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_1993,negated_conjecture,
% 11.49/2.00      ( m1_pre_topc(sK2,sK1) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_26]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2572,plain,
% 11.49/2.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_1993]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_23,negated_conjecture,
% 11.49/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 11.49/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_1996,negated_conjecture,
% 11.49/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_23]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2569,plain,
% 11.49/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_18,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 11.49/2.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 11.49/2.00      | ~ m1_pre_topc(X0,X3)
% 11.49/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.49/2.00      | ~ v2_pre_topc(X1)
% 11.49/2.00      | ~ v2_pre_topc(X3)
% 11.49/2.00      | v2_struct_0(X3)
% 11.49/2.00      | v2_struct_0(X1)
% 11.49/2.00      | v2_struct_0(X0)
% 11.49/2.00      | ~ l1_pre_topc(X3)
% 11.49/2.00      | ~ l1_pre_topc(X1)
% 11.49/2.00      | ~ v1_funct_1(X2) ),
% 11.49/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2001,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_52))
% 11.49/2.00      | ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.00      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X2_50)
% 11.49/2.00      | v2_struct_0(X0_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | v2_struct_0(X2_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X2_50)
% 11.49/2.00      | ~ v1_funct_1(X0_52) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_18]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2564,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_52)) = iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2001]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8,plain,
% 11.49/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.49/2.00      | ~ m1_pre_topc(X3,X4)
% 11.49/2.00      | ~ m1_pre_topc(X1,X4)
% 11.49/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.49/2.00      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 11.49/2.00      | ~ v2_pre_topc(X2)
% 11.49/2.00      | ~ v2_pre_topc(X4)
% 11.49/2.00      | v2_struct_0(X4)
% 11.49/2.00      | v2_struct_0(X2)
% 11.49/2.00      | ~ l1_pre_topc(X4)
% 11.49/2.00      | ~ l1_pre_topc(X2)
% 11.49/2.00      | ~ v1_funct_1(X0) ),
% 11.49/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2011,plain,
% 11.49/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.00      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.00      | ~ m1_pre_topc(X3_50,X2_50)
% 11.49/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.00      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X2_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | v2_struct_0(X2_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X2_50)
% 11.49/2.00      | ~ v1_funct_1(X0_52) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_8]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2554,plain,
% 11.49/2.00      ( v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X3_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X3_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2011]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_3,plain,
% 11.49/2.00      ( ~ r2_funct_2(X0,X1,X2,X3)
% 11.49/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.49/2.00      | ~ v1_funct_2(X3,X0,X1)
% 11.49/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.49/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.49/2.00      | ~ v1_funct_1(X2)
% 11.49/2.00      | ~ v1_funct_1(X3)
% 11.49/2.00      | X3 = X2 ),
% 11.49/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2014,plain,
% 11.49/2.00      ( ~ r2_funct_2(X0_51,X1_51,X0_52,X1_52)
% 11.49/2.00      | ~ v1_funct_2(X0_52,X0_51,X1_51)
% 11.49/2.00      | ~ v1_funct_2(X1_52,X0_51,X1_51)
% 11.49/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.00      | ~ v1_funct_1(X0_52)
% 11.49/2.00      | ~ v1_funct_1(X1_52)
% 11.49/2.00      | X1_52 = X0_52 ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_3]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2551,plain,
% 11.49/2.00      ( X0_52 = X1_52
% 11.49/2.00      | r2_funct_2(X0_51,X1_51,X1_52,X0_52) != iProver_top
% 11.49/2.00      | v1_funct_2(X1_52,X0_51,X1_51) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,X0_51,X1_51) != iProver_top
% 11.49/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.49/2.00      | v1_funct_1(X1_52) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_4997,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = X1_52
% 11.49/2.00      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),X1_52,k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(X1_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_2554,c_2551]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_10,plain,
% 11.49/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.49/2.00      | ~ m1_pre_topc(X3,X4)
% 11.49/2.00      | ~ m1_pre_topc(X1,X4)
% 11.49/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.49/2.00      | ~ v2_pre_topc(X2)
% 11.49/2.00      | ~ v2_pre_topc(X4)
% 11.49/2.00      | v2_struct_0(X4)
% 11.49/2.00      | v2_struct_0(X2)
% 11.49/2.00      | ~ l1_pre_topc(X4)
% 11.49/2.00      | ~ l1_pre_topc(X2)
% 11.49/2.00      | ~ v1_funct_1(X0)
% 11.49/2.00      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 11.49/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2009,plain,
% 11.49/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.00      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.00      | ~ m1_pre_topc(X3_50,X2_50)
% 11.49/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X2_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | v2_struct_0(X2_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X2_50)
% 11.49/2.00      | ~ v1_funct_1(X0_52)
% 11.49/2.00      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52)) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_10]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2556,plain,
% 11.49/2.00      ( v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X3_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X3_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52)) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_9,plain,
% 11.49/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.49/2.00      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 11.49/2.00      | ~ m1_pre_topc(X4,X3)
% 11.49/2.00      | ~ m1_pre_topc(X1,X3)
% 11.49/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.49/2.00      | ~ v2_pre_topc(X2)
% 11.49/2.00      | ~ v2_pre_topc(X3)
% 11.49/2.00      | v2_struct_0(X3)
% 11.49/2.00      | v2_struct_0(X2)
% 11.49/2.00      | ~ l1_pre_topc(X3)
% 11.49/2.00      | ~ l1_pre_topc(X2)
% 11.49/2.00      | ~ v1_funct_1(X0) ),
% 11.49/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2010,plain,
% 11.49/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.00      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50))
% 11.49/2.00      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.00      | ~ m1_pre_topc(X3_50,X2_50)
% 11.49/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X2_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | v2_struct_0(X2_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X2_50)
% 11.49/2.00      | ~ v1_funct_1(X0_52) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_9]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2555,plain,
% 11.49/2.00      ( v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2010]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_6978,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = X1_52
% 11.49/2.00      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),X1_52,k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.00      inference(forward_subsumption_resolution,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_4997,c_2556,c_2555]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_6982,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,X1_50,X2_50,X2_50,X0_52) = X0_52
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_2564,c_6978]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8386,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) = sK3
% 11.49/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(sK1) = iProver_top
% 11.49/2.00      | v2_struct_0(sK2) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_2569,c_6982]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_30,negated_conjecture,
% 11.49/2.00      ( ~ v2_struct_0(sK1) ),
% 11.49/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_31,plain,
% 11.49/2.00      ( v2_struct_0(sK1) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_29,negated_conjecture,
% 11.49/2.00      ( v2_pre_topc(sK1) ),
% 11.49/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_32,plain,
% 11.49/2.00      ( v2_pre_topc(sK1) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_28,negated_conjecture,
% 11.49/2.00      ( l1_pre_topc(sK1) ),
% 11.49/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_33,plain,
% 11.49/2.00      ( l1_pre_topc(sK1) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_27,negated_conjecture,
% 11.49/2.00      ( ~ v2_struct_0(sK2) ),
% 11.49/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_34,plain,
% 11.49/2.00      ( v2_struct_0(sK2) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_25,negated_conjecture,
% 11.49/2.00      ( v1_funct_1(sK3) ),
% 11.49/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_36,plain,
% 11.49/2.00      ( v1_funct_1(sK3) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_24,negated_conjecture,
% 11.49/2.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 11.49/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_37,plain,
% 11.49/2.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8483,plain,
% 11.49/2.00      ( v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.00      | k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) = sK3
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.00      inference(global_propositional_subsumption,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_8386,c_31,c_32,c_33,c_34,c_36,c_37]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8484,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) = sK3
% 11.49/2.00      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.00      inference(renaming,[status(thm)],[c_8483]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8494,plain,
% 11.49/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 11.49/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v2_struct_0(sK1) = iProver_top
% 11.49/2.00      | l1_pre_topc(sK1) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_2572,c_8484]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_35,plain,
% 11.49/2.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8474,plain,
% 11.49/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 11.49/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v2_struct_0(sK1) = iProver_top
% 11.49/2.00      | v2_struct_0(sK2) = iProver_top
% 11.49/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.00      inference(instantiation,[status(thm)],[c_8386]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_8541,plain,
% 11.49/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
% 11.49/2.00      inference(global_propositional_subsumption,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_8494,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_8474]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_17,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5)
% 11.49/2.00      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 11.49/2.00      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 11.49/2.00      | ~ m1_pre_topc(X3,X2)
% 11.49/2.00      | ~ m1_pre_topc(X0,X2)
% 11.49/2.00      | ~ m1_pre_topc(X0,X3)
% 11.49/2.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.49/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.49/2.00      | m1_subset_1(sK0(X1,X0,X3,X4,X5),u1_struct_0(X3))
% 11.49/2.00      | ~ v2_pre_topc(X1)
% 11.49/2.00      | ~ v2_pre_topc(X2)
% 11.49/2.00      | v2_struct_0(X2)
% 11.49/2.00      | v2_struct_0(X1)
% 11.49/2.00      | v2_struct_0(X0)
% 11.49/2.00      | v2_struct_0(X3)
% 11.49/2.00      | ~ l1_pre_topc(X2)
% 11.49/2.00      | ~ l1_pre_topc(X1)
% 11.49/2.00      | ~ v1_funct_1(X4)
% 11.49/2.00      | ~ v1_funct_1(X5) ),
% 11.49/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2002,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
% 11.49/2.00      | ~ v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.00      | ~ v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50))
% 11.49/2.00      | ~ m1_pre_topc(X0_50,X3_50)
% 11.49/2.00      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.00      | ~ m1_pre_topc(X3_50,X2_50)
% 11.49/2.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 11.49/2.00      | m1_subset_1(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X3_50))
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X2_50)
% 11.49/2.00      | v2_struct_0(X0_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | v2_struct_0(X3_50)
% 11.49/2.00      | v2_struct_0(X2_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X2_50)
% 11.49/2.00      | ~ v1_funct_1(X0_52)
% 11.49/2.00      | ~ v1_funct_1(X1_52) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_17]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2563,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
% 11.49/2.00      | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X3_50)) = iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2002]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_19,plain,
% 11.49/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.49/2.00      | ~ m1_pre_topc(X2,X0)
% 11.49/2.00      | m1_pre_topc(X2,X1)
% 11.49/2.00      | ~ v2_pre_topc(X1)
% 11.49/2.00      | ~ l1_pre_topc(X1) ),
% 11.49/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2000,plain,
% 11.49/2.00      ( ~ m1_pre_topc(X0_50,X1_50)
% 11.49/2.00      | ~ m1_pre_topc(X2_50,X0_50)
% 11.49/2.00      | m1_pre_topc(X2_50,X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_19]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2565,plain,
% 11.49/2.00      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X1_50) = iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2881,plain,
% 11.49/2.00      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
% 11.49/2.00      | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X3_50)) = iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.00      inference(forward_subsumption_resolution,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_2563,c_2565]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_11,plain,
% 11.49/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.49/2.00      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.49/2.00      | ~ v2_pre_topc(X1)
% 11.49/2.00      | v2_struct_0(X1)
% 11.49/2.00      | ~ l1_pre_topc(X1) ),
% 11.49/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2008,plain,
% 11.49/2.00      ( ~ m1_pre_topc(X0_50,X1_50)
% 11.49/2.00      | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_11]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2557,plain,
% 11.49/2.00      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.00      | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) = iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_4087,plain,
% 11.49/2.00      ( k4_tmap_1(X0_50,X1_50) = X0_52
% 11.49/2.00      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_2557,c_2551]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_12,plain,
% 11.49/2.00      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 11.49/2.00      | ~ m1_pre_topc(X1,X0)
% 11.49/2.00      | ~ v2_pre_topc(X0)
% 11.49/2.00      | v2_struct_0(X0)
% 11.49/2.00      | ~ l1_pre_topc(X0) ),
% 11.49/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2007,plain,
% 11.49/2.00      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
% 11.49/2.00      | ~ m1_pre_topc(X1_50,X0_50)
% 11.49/2.00      | ~ v2_pre_topc(X0_50)
% 11.49/2.00      | v2_struct_0(X0_50)
% 11.49/2.00      | ~ l1_pre_topc(X0_50) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_12]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2059,plain,
% 11.49/2.00      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.00      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2007]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_5690,plain,
% 11.49/2.00      ( v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.00      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
% 11.49/2.00      | k4_tmap_1(X0_50,X1_50) = X0_52
% 11.49/2.00      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top ),
% 11.49/2.00      inference(global_propositional_subsumption,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_4087,c_2059]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_5691,plain,
% 11.49/2.00      ( k4_tmap_1(X0_50,X1_50) = X0_52
% 11.49/2.00      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top ),
% 11.49/2.00      inference(renaming,[status(thm)],[c_5690]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_13,plain,
% 11.49/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.49/2.00      | ~ v2_pre_topc(X1)
% 11.49/2.00      | v2_struct_0(X1)
% 11.49/2.00      | ~ l1_pre_topc(X1)
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 11.49/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2006,plain,
% 11.49/2.00      ( ~ m1_pre_topc(X0_50,X1_50)
% 11.49/2.00      | ~ v2_pre_topc(X1_50)
% 11.49/2.00      | v2_struct_0(X1_50)
% 11.49/2.00      | ~ l1_pre_topc(X1_50)
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) ),
% 11.49/2.00      inference(subtyping,[status(esa)],[c_13]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2559,plain,
% 11.49/2.00      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_5706,plain,
% 11.49/2.00      ( k4_tmap_1(X0_50,X1_50) = X0_52
% 11.49/2.00      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),X0_52,k4_tmap_1(X0_50,X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.00      inference(forward_subsumption_resolution,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_5691,c_2559]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_6253,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(k4_tmap_1(X1_50,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X1_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X2_50)) = iProver_top
% 11.49/2.00      | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(k4_tmap_1(X1_50,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
% 11.49/2.00      | v1_funct_1(k4_tmap_1(X1_50,X3_50)) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_2881,c_5706]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2558,plain,
% 11.49/2.00      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.00      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_2007]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_22680,plain,
% 11.49/2.00      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
% 11.49/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.00      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.00      | m1_pre_topc(X3_50,X1_50) != iProver_top
% 11.49/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | m1_subset_1(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X2_50)) = iProver_top
% 11.49/2.00      | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.00      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.00      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.00      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.00      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top ),
% 11.49/2.00      inference(forward_subsumption_resolution,
% 11.49/2.00                [status(thm)],
% 11.49/2.00                [c_6253,c_2559,c_2557,c_2558]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_22686,plain,
% 11.49/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k4_tmap_1(sK1,sK2)
% 11.49/2.00      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.00      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
% 11.49/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v2_struct_0(sK1) = iProver_top
% 11.49/2.00      | v2_struct_0(sK2) = iProver_top
% 11.49/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
% 11.49/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.00      inference(superposition,[status(thm)],[c_8541,c_22680]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_22701,plain,
% 11.49/2.00      ( k4_tmap_1(sK1,sK2) = sK3
% 11.49/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.00      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
% 11.49/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v2_struct_0(sK1) = iProver_top
% 11.49/2.00      | v2_struct_0(sK2) = iProver_top
% 11.49/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.00      inference(light_normalisation,[status(thm)],[c_22686,c_8541]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_38,plain,
% 11.49/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 11.49/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_21,negated_conjecture,
% 11.49/2.00      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 11.49/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2019,plain,( X0_52 = X0_52 ),theory(equality) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2036,plain,
% 11.49/2.00      ( sK3 = sK3 ),
% 11.49/2.00      inference(instantiation,[status(thm)],[c_2019]) ).
% 11.49/2.00  
% 11.49/2.00  cnf(c_2,plain,
% 11.49/2.00      ( r2_funct_2(X0,X1,X2,X2)
% 11.49/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.49/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.49/2.01      | ~ v1_funct_1(X2) ),
% 11.49/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2015,plain,
% 11.49/2.01      ( r2_funct_2(X0_51,X1_51,X0_52,X0_52)
% 11.49/2.01      | ~ v1_funct_2(X0_52,X0_51,X1_51)
% 11.49/2.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.01      | ~ v1_funct_1(X0_52) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_2]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3035,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.49/2.01      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v1_funct_1(sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2015]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2027,plain,
% 11.49/2.01      ( ~ r2_funct_2(X0_51,X1_51,X0_52,X1_52)
% 11.49/2.01      | r2_funct_2(X0_51,X1_51,X2_52,X3_52)
% 11.49/2.01      | X2_52 != X0_52
% 11.49/2.01      | X3_52 != X1_52 ),
% 11.49/2.01      theory(equality) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3131,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
% 11.49/2.01      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.49/2.01      | X0_52 != sK3
% 11.49/2.01      | X1_52 != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2027]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3332,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 11.49/2.01      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.49/2.01      | k4_tmap_1(sK1,sK2) != sK3
% 11.49/2.01      | sK3 != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3131]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5,plain,
% 11.49/2.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.49/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2013,plain,
% 11.49/2.01      ( ~ m1_pre_topc(X0_50,X1_50)
% 11.49/2.01      | ~ l1_pre_topc(X1_50)
% 11.49/2.01      | l1_pre_topc(X0_50) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_5]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2552,plain,
% 11.49/2.01      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) = iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3366,plain,
% 11.49/2.01      ( l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK2) = iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2572,c_2552]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_14,plain,
% 11.49/2.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.49/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2005,plain,
% 11.49/2.01      ( m1_pre_topc(X0_50,X0_50) | ~ l1_pre_topc(X0_50) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_14]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3845,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2005]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3846,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK2) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_3845]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_23908,plain,
% 11.49/2.01      ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_22701,c_31,c_32,c_33,c_34,c_35,c_25,c_36,c_24,c_37,
% 11.49/2.01                 c_23,c_38,c_21,c_2036,c_3035,c_3332,c_3366,c_3846]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7,plain,
% 11.49/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.49/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.49/2.01      | m1_subset_1(X2,u1_struct_0(X1))
% 11.49/2.01      | v2_struct_0(X1)
% 11.49/2.01      | v2_struct_0(X0)
% 11.49/2.01      | ~ l1_pre_topc(X1) ),
% 11.49/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2012,plain,
% 11.49/2.01      ( ~ m1_pre_topc(X0_50,X1_50)
% 11.49/2.01      | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X1_50))
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(X1_50)
% 11.49/2.01      | ~ l1_pre_topc(X1_50) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_7]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2553,plain,
% 11.49/2.01      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X1_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_2012]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_23917,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_23908,c_2553]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22979,plain,
% 11.49/2.01      ( ~ m1_pre_topc(sK2,X0_50)
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50))
% 11.49/2.01      | ~ m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2))
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(sK2)
% 11.49/2.01      | ~ l1_pre_topc(X0_50) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2012]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22980,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_22979]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_24569,plain,
% 11.49/2.01      ( v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_23917,c_31,c_32,c_33,c_34,c_35,c_25,c_36,c_24,c_37,
% 11.49/2.01                 c_23,c_38,c_21,c_2036,c_3035,c_3332,c_3366,c_3846,
% 11.49/2.01                 c_22701,c_22980]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_24570,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_24569]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22,negated_conjecture,
% 11.49/2.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 11.49/2.01      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 11.49/2.01      | k1_funct_1(sK3,X0) = X0 ),
% 11.49/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_1997,negated_conjecture,
% 11.49/2.01      ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
% 11.49/2.01      | ~ r2_hidden(X0_52,u1_struct_0(sK2))
% 11.49/2.01      | k1_funct_1(sK3,X0_52) = X0_52 ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_22]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2568,plain,
% 11.49/2.01      ( k1_funct_1(sK3,X0_52) = X0_52
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_24579,plain,
% 11.49/2.01      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_24570,c_2568]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_8648,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_8541,c_2881]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9051,plain,
% 11.49/2.01      ( v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_8648,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3366,
% 11.49/2.01                 c_3846]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9052,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_9051]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9064,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_9052,c_2553]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10434,plain,
% 11.49/2.01      ( v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_9064,c_34]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10435,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_10434]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10446,plain,
% 11.49/2.01      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_10435,c_2568]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_16,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5)
% 11.49/2.01      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 11.49/2.01      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 11.49/2.01      | ~ m1_pre_topc(X3,X2)
% 11.49/2.01      | ~ m1_pre_topc(X0,X2)
% 11.49/2.01      | ~ m1_pre_topc(X0,X3)
% 11.49/2.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.49/2.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.49/2.01      | r2_hidden(sK0(X1,X0,X3,X4,X5),u1_struct_0(X0))
% 11.49/2.01      | ~ v2_pre_topc(X1)
% 11.49/2.01      | ~ v2_pre_topc(X2)
% 11.49/2.01      | v2_struct_0(X2)
% 11.49/2.01      | v2_struct_0(X1)
% 11.49/2.01      | v2_struct_0(X0)
% 11.49/2.01      | v2_struct_0(X3)
% 11.49/2.01      | ~ l1_pre_topc(X2)
% 11.49/2.01      | ~ l1_pre_topc(X1)
% 11.49/2.01      | ~ v1_funct_1(X4)
% 11.49/2.01      | ~ v1_funct_1(X5) ),
% 11.49/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2003,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
% 11.49/2.01      | ~ v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.01      | ~ v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50))
% 11.49/2.01      | ~ m1_pre_topc(X0_50,X3_50)
% 11.49/2.01      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.01      | ~ m1_pre_topc(X3_50,X2_50)
% 11.49/2.01      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 11.49/2.01      | r2_hidden(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X0_50))
% 11.49/2.01      | ~ v2_pre_topc(X1_50)
% 11.49/2.01      | ~ v2_pre_topc(X2_50)
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(X1_50)
% 11.49/2.01      | v2_struct_0(X3_50)
% 11.49/2.01      | v2_struct_0(X2_50)
% 11.49/2.01      | ~ l1_pre_topc(X1_50)
% 11.49/2.01      | ~ l1_pre_topc(X2_50)
% 11.49/2.01      | ~ v1_funct_1(X0_52)
% 11.49/2.01      | ~ v1_funct_1(X1_52) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_16]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2562,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_2003]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2843,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(X1_50,X0_50,X3_50,X0_52,X1_52),u1_struct_0(X0_50)) = iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(forward_subsumption_resolution,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_2562,c_2565]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_8649,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_8541,c_2843]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9539,plain,
% 11.49/2.01      ( v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_8649,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3366,
% 11.49/2.01                 c_3846]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9540,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_9539]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10927,plain,
% 11.49/2.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_10446,c_31,c_33,c_35,c_9540]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10928,plain,
% 11.49/2.01      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_10927]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10937,plain,
% 11.49/2.01      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2557,c_10928]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5782,plain,
% 11.49/2.01      ( ~ m1_pre_topc(sK2,sK1)
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | ~ l1_pre_topc(sK1)
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2006]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5783,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_5782]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3264,plain,
% 11.49/2.01      ( v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_pre_topc(X0_50,sK1)
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | ~ l1_pre_topc(sK1) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2007]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5807,plain,
% 11.49/2.01      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_pre_topc(sK2,sK1)
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | ~ l1_pre_topc(sK1) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3264]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5810,plain,
% 11.49/2.01      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_5807]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10990,plain,
% 11.49/2.01      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_10937,c_31,c_32,c_33,c_35,c_5783,c_5810]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10996,plain,
% 11.49/2.01      ( k4_tmap_1(sK1,sK2) = sK3
% 11.49/2.01      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_10990,c_5706]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_25127,plain,
% 11.49/2.01      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_24579,c_31,c_32,c_33,c_35,c_25,c_36,c_24,c_37,c_23,
% 11.49/2.01                 c_38,c_21,c_2036,c_3035,c_3332,c_10996]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_1,plain,
% 11.49/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.49/2.01      | ~ m1_subset_1(X3,X1)
% 11.49/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.49/2.01      | ~ v1_funct_1(X0)
% 11.49/2.01      | v1_xboole_0(X1)
% 11.49/2.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 11.49/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2016,plain,
% 11.49/2.01      ( ~ v1_funct_2(X0_52,X0_51,X1_51)
% 11.49/2.01      | ~ m1_subset_1(X1_52,X0_51)
% 11.49/2.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.01      | ~ v1_funct_1(X0_52)
% 11.49/2.01      | v1_xboole_0(X0_51)
% 11.49/2.01      | k3_funct_2(X0_51,X1_51,X0_52,X1_52) = k1_funct_1(X0_52,X1_52) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_1]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2549,plain,
% 11.49/2.01      ( k3_funct_2(X0_51,X1_51,X0_52,X1_52) = k1_funct_1(X0_52,X1_52)
% 11.49/2.01      | v1_funct_2(X0_52,X0_51,X1_51) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,X0_51) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_xboole_0(X0_51) = iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_4996,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = k1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52)) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2554,c_2549]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5830,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52) = k1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 11.49/2.01      inference(forward_subsumption_resolution,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_4996,c_2556,c_2555]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5834,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52)
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2569,c_5830]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5943,plain,
% 11.49/2.01      ( v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52)
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_5834,c_31,c_32,c_33,c_36,c_37]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5944,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),X0_52)
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_5943]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_6247,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k3_tmap_1(X4_50,X2_50,X0_50,X3_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X4_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X4_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X4_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X4_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2881,c_5944]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2047,plain,
% 11.49/2.01      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) = iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_4,plain,
% 11.49/2.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.49/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_6,plain,
% 11.49/2.01      ( v2_struct_0(X0)
% 11.49/2.01      | ~ l1_struct_0(X0)
% 11.49/2.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.49/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_338,plain,
% 11.49/2.01      ( v2_struct_0(X0)
% 11.49/2.01      | ~ l1_pre_topc(X0)
% 11.49/2.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.49/2.01      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_1988,plain,
% 11.49/2.01      ( v2_struct_0(X0_50)
% 11.49/2.01      | ~ l1_pre_topc(X0_50)
% 11.49/2.01      | ~ v1_xboole_0(u1_struct_0(X0_50)) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_338]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2090,plain,
% 11.49/2.01      ( v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7734,plain,
% 11.49/2.01      ( v1_funct_1(X1_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X4_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X4_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X4_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X4_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k3_tmap_1(X4_50,X2_50,X0_50,X3_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_6247,c_2047,c_2090]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7735,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3),sK0(X2_50,X3_50,X0_50,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k3_tmap_1(X4_50,X2_50,X0_50,X3_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X4_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X4_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X4_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X4_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_7734]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7763,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X1_50,sK2) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2572,c_7735]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7856,plain,
% 11.49/2.01      ( l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X1_50,sK2) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52))
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_7763,c_31,c_32,c_33,c_34,c_35]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7857,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0_50,X1_50,sK2,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X1_50,sK2) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_7856]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_7880,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52) = k4_tmap_1(X1_50,X2_50)
% 11.49/2.01      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50)))
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(X1_50,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,sK2) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(X1_50,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52)) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(X1_50,X2_50)) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_7857,c_5706]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_8179,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52) = k4_tmap_1(X1_50,X2_50)
% 11.49/2.01      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50)))
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,sK2) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52)) != iProver_top ),
% 11.49/2.01      inference(forward_subsumption_resolution,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_7880,c_2559,c_2557,c_2558]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_8544,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52) = k4_tmap_1(X1_50,X2_50)
% 11.49/2.01      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50))) = k1_funct_1(sK3,sK0(X1_50,X2_50,sK2,X0_52,k4_tmap_1(X1_50,X2_50)))
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,sK2) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,X1_50,sK2,X2_50,X0_52)) != iProver_top ),
% 11.49/2.01      inference(demodulation,[status(thm)],[c_8541,c_8179]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12118,plain,
% 11.49/2.01      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k4_tmap_1(sK1,sK2)
% 11.49/2.01      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.49/2.01      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_8541,c_8544]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12132,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.49/2.01      | k4_tmap_1(sK1,sK2) = sK3
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(light_normalisation,[status(thm)],[c_12118,c_8541]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_8546,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,X1_50,sK2,X0_52,X1_52)) = k1_funct_1(sK3,sK0(X0_50,X1_50,sK2,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k3_tmap_1(X2_50,X0_50,sK2,X1_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X1_50,sK2) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X2_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X2_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(demodulation,[status(thm)],[c_8541,c_7857]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9940,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_8541,c_8546]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10097,plain,
% 11.49/2.01      ( v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_9940,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3366,
% 11.49/2.01                 c_3846]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10098,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_10097]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10107,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2557,c_10098]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10841,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_10107,c_31,c_32,c_33,c_35,c_5783,c_5810]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10847,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.49/2.01      | k4_tmap_1(sK1,sK2) = sK3
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_10841,c_5706]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12185,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_12132,c_31,c_32,c_33,c_35,c_25,c_36,c_24,c_37,c_23,
% 11.49/2.01                 c_38,c_21,c_2036,c_3035,c_3332,c_10847]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_25130,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 11.49/2.01      inference(demodulation,[status(thm)],[c_25127,c_12185]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_15,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5)
% 11.49/2.01      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 11.49/2.01      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 11.49/2.01      | ~ m1_pre_topc(X3,X2)
% 11.49/2.01      | ~ m1_pre_topc(X0,X2)
% 11.49/2.01      | ~ m1_pre_topc(X0,X3)
% 11.49/2.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.49/2.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.49/2.01      | ~ v2_pre_topc(X1)
% 11.49/2.01      | ~ v2_pre_topc(X2)
% 11.49/2.01      | v2_struct_0(X2)
% 11.49/2.01      | v2_struct_0(X1)
% 11.49/2.01      | v2_struct_0(X0)
% 11.49/2.01      | v2_struct_0(X3)
% 11.49/2.01      | ~ l1_pre_topc(X2)
% 11.49/2.01      | ~ l1_pre_topc(X1)
% 11.49/2.01      | ~ v1_funct_1(X4)
% 11.49/2.01      | ~ v1_funct_1(X5)
% 11.49/2.01      | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK0(X1,X0,X3,X4,X5)) != k1_funct_1(X5,sK0(X1,X0,X3,X4,X5)) ),
% 11.49/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2004,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_52),X1_52)
% 11.49/2.01      | ~ v1_funct_2(X1_52,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.01      | ~ v1_funct_2(X0_52,u1_struct_0(X3_50),u1_struct_0(X1_50))
% 11.49/2.01      | ~ m1_pre_topc(X0_50,X3_50)
% 11.49/2.01      | ~ m1_pre_topc(X0_50,X2_50)
% 11.49/2.01      | ~ m1_pre_topc(X3_50,X2_50)
% 11.49/2.01      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 11.49/2.01      | ~ v2_pre_topc(X1_50)
% 11.49/2.01      | ~ v2_pre_topc(X2_50)
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(X1_50)
% 11.49/2.01      | v2_struct_0(X3_50)
% 11.49/2.01      | v2_struct_0(X2_50)
% 11.49/2.01      | ~ l1_pre_topc(X1_50)
% 11.49/2.01      | ~ l1_pre_topc(X2_50)
% 11.49/2.01      | ~ v1_funct_1(X0_52)
% 11.49/2.01      | ~ v1_funct_1(X1_52)
% 11.49/2.01      | k3_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),X0_52,sK0(X1_50,X0_50,X3_50,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_50,X0_50,X3_50,X0_52,X1_52)) ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_15]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2561,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X3_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X3_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_2004]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2919,plain,
% 11.49/2.01      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_50,X2_50,X0_50,X0_52,X1_52))
% 11.49/2.01      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_52),X1_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(X1_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X3_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X3_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(X1_52) != iProver_top ),
% 11.49/2.01      inference(forward_subsumption_resolution,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_2561,c_2565]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_25552,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_25130,c_2919]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_10451,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_10435,c_2553]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_18925,plain,
% 11.49/2.01      ( v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_50)) = iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_10451,c_2047]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_18926,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_50)) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_18925]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_18939,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2572,c_18926]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_19015,plain,
% 11.49/2.01      ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_18939,c_31,c_33,c_34,c_3366,c_3846]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_19016,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_19015]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_6115,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(X1_50,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X1_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(X1_50,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X3_50)) = iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(X1_50,X3_50)) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_2843,c_5706]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12384,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52) = k4_tmap_1(X1_50,X3_50)
% 11.49/2.01      | v1_funct_2(X0_52,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(X3_50,X1_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(X1_50,X3_50,X2_50,X0_52,k4_tmap_1(X1_50,X3_50)),u1_struct_0(X3_50)) = iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X3_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X2_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(X1_50) != iProver_top
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_52)) != iProver_top ),
% 11.49/2.01      inference(forward_subsumption_resolution,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_6115,c_2559,c_2557,c_2558]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12389,plain,
% 11.49/2.01      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k4_tmap_1(sK1,sK2)
% 11.49/2.01      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_8541,c_12384]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12403,plain,
% 11.49/2.01      ( k4_tmap_1(sK1,sK2) = sK3
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(light_normalisation,[status(thm)],[c_12389,c_8541]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_13477,plain,
% 11.49/2.01      ( r2_hidden(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_12403,c_31,c_32,c_33,c_34,c_35,c_25,c_36,c_24,c_37,
% 11.49/2.01                 c_23,c_38,c_21,c_2036,c_3035,c_3332,c_3366,c_3846]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_20,plain,
% 11.49/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.49/2.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.49/2.01      | ~ r2_hidden(X2,u1_struct_0(X0))
% 11.49/2.01      | ~ v2_pre_topc(X1)
% 11.49/2.01      | v2_struct_0(X1)
% 11.49/2.01      | v2_struct_0(X0)
% 11.49/2.01      | ~ l1_pre_topc(X1)
% 11.49/2.01      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 11.49/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_1999,plain,
% 11.49/2.01      ( ~ m1_pre_topc(X0_50,X1_50)
% 11.49/2.01      | ~ m1_subset_1(X0_52,u1_struct_0(X1_50))
% 11.49/2.01      | ~ r2_hidden(X0_52,u1_struct_0(X0_50))
% 11.49/2.01      | ~ v2_pre_topc(X1_50)
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(X1_50)
% 11.49/2.01      | ~ l1_pre_topc(X1_50)
% 11.49/2.01      | k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_52) = X0_52 ),
% 11.49/2.01      inference(subtyping,[status(esa)],[c_20]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2566,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(X0_50,X1_50),X0_52) = X0_52
% 11.49/2.01      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | r2_hidden(X0_52,u1_struct_0(X1_50)) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X1_50) = iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_1999]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_13482,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_13477,c_2566]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_14167,plain,
% 11.49/2.01      ( v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_13482,c_34]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_14168,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)),u1_struct_0(X0_50)) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top ),
% 11.49/2.01      inference(renaming,[status(thm)],[c_14167]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_19031,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_19016,c_14168]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12067,plain,
% 11.49/2.01      ( ~ m1_pre_topc(sK2,sK1)
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | ~ l1_pre_topc(sK1) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2008]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12068,plain,
% 11.49/2.01      ( m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_12067]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3832,plain,
% 11.49/2.01      ( ~ r2_funct_2(X0_51,X1_51,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),X0_51,X1_51)
% 11.49/2.01      | ~ v1_funct_2(sK3,X0_51,X1_51)
% 11.49/2.01      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.01      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 11.49/2.01      | ~ v1_funct_1(sK3)
% 11.49/2.01      | k4_tmap_1(sK1,sK2) = sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2014]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_13501,plain,
% 11.49/2.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 11.49/2.01      | ~ v1_funct_1(sK3)
% 11.49/2.01      | k4_tmap_1(sK1,sK2) = sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3832]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_13502,plain,
% 11.49/2.01      ( k4_tmap_1(sK1,sK2) = sK3
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_13501]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_14181,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(X0_50,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(superposition,[status(thm)],[c_10435,c_14168]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_14242,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_14181]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_19743,plain,
% 11.49/2.01      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 11.49/2.01      inference(global_propositional_subsumption,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_19031,c_31,c_32,c_33,c_35,c_25,c_36,c_24,c_37,c_23,
% 11.49/2.01                 c_38,c_21,c_2036,c_3035,c_3332,c_5783,c_5810,c_12068,
% 11.49/2.01                 c_13502,c_14242]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_25553,plain,
% 11.49/2.01      ( sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(light_normalisation,[status(thm)],[c_25552,c_19743]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_25554,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(equality_resolution_simp,[status(thm)],[c_25553]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_25556,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) = iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | v2_struct_0(sK2) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_25554]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3373,plain,
% 11.49/2.01      ( ~ r2_funct_2(X0_51,X1_51,k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_52)
% 11.49/2.01      | ~ v1_funct_2(X0_52,X0_51,X1_51)
% 11.49/2.01      | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51,X1_51)
% 11.49/2.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.01      | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.49/2.01      | ~ v1_funct_1(X0_52)
% 11.49/2.01      | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3))
% 11.49/2.01      | X0_52 = k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2014]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_4312,plain,
% 11.49/2.01      ( ~ r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3),k4_tmap_1(X1_50,X0_50))
% 11.49/2.01      | ~ v1_funct_2(k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3),u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.01      | ~ v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.49/2.01      | ~ m1_subset_1(k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.01      | ~ m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.49/2.01      | ~ v1_funct_1(k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3))
% 11.49/2.01      | ~ v1_funct_1(k4_tmap_1(X1_50,X0_50))
% 11.49/2.01      | k4_tmap_1(X1_50,X0_50) = k3_tmap_1(X2_50,sK1,sK2,X3_50,sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3373]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_9032,plain,
% 11.49/2.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),k4_tmap_1(sK1,sK2))
% 11.49/2.01      | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3))
% 11.49/2.01      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 11.49/2.01      | k4_tmap_1(sK1,sK2) = k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_4312]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_24820,plain,
% 11.49/2.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2))
% 11.49/2.01      | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
% 11.49/2.01      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 11.49/2.01      | k4_tmap_1(sK1,sK2) = k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_9032]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_24821,plain,
% 11.49/2.01      ( k4_tmap_1(sK1,sK2) = k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_24820]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_24823,plain,
% 11.49/2.01      ( k4_tmap_1(sK1,sK2) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k4_tmap_1(sK1,sK2)) != iProver_top
% 11.49/2.01      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_subset_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
% 11.49/2.01      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_24821]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2022,plain,
% 11.49/2.01      ( ~ m1_subset_1(X0_52,X0_51)
% 11.49/2.01      | m1_subset_1(X1_52,X0_51)
% 11.49/2.01      | X1_52 != X0_52 ),
% 11.49/2.01      theory(equality) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3010,plain,
% 11.49/2.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | X0_52 != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2022]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22997,plain,
% 11.49/2.01      ( m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3010]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22998,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != sK3
% 11.49/2.01      | m1_subset_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_22997]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_23000,plain,
% 11.49/2.01      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) != sK3
% 11.49/2.01      | m1_subset_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_22998]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3170,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
% 11.49/2.01      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
% 11.49/2.01      | X1_52 != k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)
% 11.49/2.01      | X0_52 != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2027]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22326,plain,
% 11.49/2.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | k4_tmap_1(sK1,sK2) != k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)
% 11.49/2.01      | sK3 != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3170]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_22331,plain,
% 11.49/2.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK1,sK1,sK2,sK2,sK3))
% 11.49/2.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 11.49/2.01      | k4_tmap_1(sK1,sK2) != k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 11.49/2.01      | sK3 != sK3 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_22326]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_2026,plain,
% 11.49/2.01      ( ~ v1_funct_1(X0_52) | v1_funct_1(X1_52) | X1_52 != X0_52 ),
% 11.49/2.01      theory(equality) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12006,plain,
% 11.49/2.01      ( ~ v1_funct_1(X0_52)
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
% 11.49/2.01      | k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != X0_52 ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2026]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12007,plain,
% 11.49/2.01      ( k3_tmap_1(X0_50,sK1,sK2,sK2,sK3) != X0_52
% 11.49/2.01      | v1_funct_1(X0_52) != iProver_top
% 11.49/2.01      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3)) = iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_12006]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_12009,plain,
% 11.49/2.01      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) != sK3
% 11.49/2.01      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) = iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_12007]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3077,plain,
% 11.49/2.01      ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),u1_struct_0(X1_50),u1_struct_0(sK1))
% 11.49/2.01      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_pre_topc(X1_50,X0_50)
% 11.49/2.01      | ~ m1_pre_topc(sK2,X0_50)
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v2_pre_topc(X0_50)
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | ~ l1_pre_topc(X0_50)
% 11.49/2.01      | ~ l1_pre_topc(sK1)
% 11.49/2.01      | ~ v1_funct_1(sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2010]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5591,plain,
% 11.49/2.01      ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_pre_topc(sK2,X0_50)
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v2_pre_topc(X0_50)
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | ~ l1_pre_topc(X0_50)
% 11.49/2.01      | ~ l1_pre_topc(sK1)
% 11.49/2.01      | ~ v1_funct_1(sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3077]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5596,plain,
% 11.49/2.01      ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(X0_50) = iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(X0_50) != iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(predicate_to_equality,[status(thm)],[c_5591]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_5598,plain,
% 11.49/2.01      ( v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 11.49/2.01      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.49/2.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.49/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.49/2.01      | v2_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v2_struct_0(sK1) = iProver_top
% 11.49/2.01      | l1_pre_topc(sK1) != iProver_top
% 11.49/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_5596]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3067,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,sK2,sK2,sK3))
% 11.49/2.01      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_pre_topc(sK2,X0_50)
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v2_pre_topc(X0_50)
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(X0_50)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | v2_struct_0(sK2)
% 11.49/2.01      | ~ l1_pre_topc(X0_50)
% 11.49/2.01      | ~ l1_pre_topc(sK1)
% 11.49/2.01      | ~ v1_funct_1(sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_2001]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(c_3069,plain,
% 11.49/2.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK1,sK1,sK2,sK2,sK3))
% 11.49/2.01      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.49/2.01      | ~ m1_pre_topc(sK2,sK1)
% 11.49/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.49/2.01      | ~ v2_pre_topc(sK1)
% 11.49/2.01      | v2_struct_0(sK1)
% 11.49/2.01      | v2_struct_0(sK2)
% 11.49/2.01      | ~ l1_pre_topc(sK1)
% 11.49/2.01      | ~ v1_funct_1(sK3) ),
% 11.49/2.01      inference(instantiation,[status(thm)],[c_3067]) ).
% 11.49/2.01  
% 11.49/2.01  cnf(contradiction,plain,
% 11.49/2.01      ( $false ),
% 11.49/2.01      inference(minisat,
% 11.49/2.01                [status(thm)],
% 11.49/2.01                [c_25556,c_24823,c_23000,c_22331,c_13501,c_12068,c_12067,
% 11.49/2.01                 c_12009,c_8474,c_5810,c_5807,c_5783,c_5782,c_5598,
% 11.49/2.01                 c_3846,c_3366,c_3332,c_3069,c_3035,c_2036,c_21,c_38,
% 11.49/2.01                 c_23,c_37,c_24,c_36,c_25,c_35,c_26,c_34,c_27,c_33,c_28,
% 11.49/2.01                 c_32,c_29,c_31,c_30]) ).
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.49/2.01  
% 11.49/2.01  ------                               Statistics
% 11.49/2.01  
% 11.49/2.01  ------ General
% 11.49/2.01  
% 11.49/2.01  abstr_ref_over_cycles:                  0
% 11.49/2.01  abstr_ref_under_cycles:                 0
% 11.49/2.01  gc_basic_clause_elim:                   0
% 11.49/2.01  forced_gc_time:                         0
% 11.49/2.01  parsing_time:                           0.022
% 11.49/2.01  unif_index_cands_time:                  0.
% 11.49/2.01  unif_index_add_time:                    0.
% 11.49/2.01  orderings_time:                         0.
% 11.49/2.01  out_proof_time:                         0.029
% 11.49/2.01  total_time:                             1.138
% 11.49/2.01  num_of_symbols:                         57
% 11.49/2.01  num_of_terms:                           29353
% 11.49/2.01  
% 11.49/2.01  ------ Preprocessing
% 11.49/2.01  
% 11.49/2.01  num_of_splits:                          0
% 11.49/2.01  num_of_split_atoms:                     0
% 11.49/2.01  num_of_reused_defs:                     0
% 11.49/2.01  num_eq_ax_congr_red:                    54
% 11.49/2.01  num_of_sem_filtered_clauses:            1
% 11.49/2.01  num_of_subtypes:                        4
% 11.49/2.01  monotx_restored_types:                  1
% 11.49/2.01  sat_num_of_epr_types:                   0
% 11.49/2.01  sat_num_of_non_cyclic_types:            0
% 11.49/2.01  sat_guarded_non_collapsed_types:        1
% 11.49/2.01  num_pure_diseq_elim:                    0
% 11.49/2.01  simp_replaced_by:                       0
% 11.49/2.01  res_preprocessed:                       140
% 11.49/2.01  prep_upred:                             0
% 11.49/2.01  prep_unflattend:                        70
% 11.49/2.01  smt_new_axioms:                         0
% 11.49/2.01  pred_elim_cands:                        10
% 11.49/2.01  pred_elim:                              1
% 11.49/2.01  pred_elim_cl:                           1
% 11.49/2.01  pred_elim_cycles:                       7
% 11.49/2.01  merged_defs:                            0
% 11.49/2.01  merged_defs_ncl:                        0
% 11.49/2.01  bin_hyper_res:                          0
% 11.49/2.01  prep_cycles:                            4
% 11.49/2.01  pred_elim_time:                         0.053
% 11.49/2.01  splitting_time:                         0.
% 11.49/2.01  sem_filter_time:                        0.
% 11.49/2.01  monotx_time:                            0.001
% 11.49/2.01  subtype_inf_time:                       0.002
% 11.49/2.01  
% 11.49/2.01  ------ Problem properties
% 11.49/2.01  
% 11.49/2.01  clauses:                                30
% 11.49/2.01  conjectures:                            10
% 11.49/2.01  epr:                                    10
% 11.49/2.01  horn:                                   16
% 11.49/2.01  ground:                                 9
% 11.49/2.01  unary:                                  9
% 11.49/2.01  binary:                                 1
% 11.49/2.01  lits:                                   180
% 11.49/2.01  lits_eq:                                5
% 11.49/2.01  fd_pure:                                0
% 11.49/2.01  fd_pseudo:                              0
% 11.49/2.01  fd_cond:                                0
% 11.49/2.01  fd_pseudo_cond:                         1
% 11.49/2.01  ac_symbols:                             0
% 11.49/2.01  
% 11.49/2.01  ------ Propositional Solver
% 11.49/2.01  
% 11.49/2.01  prop_solver_calls:                      28
% 11.49/2.01  prop_fast_solver_calls:                 5042
% 11.49/2.01  smt_solver_calls:                       0
% 11.49/2.01  smt_fast_solver_calls:                  0
% 11.49/2.01  prop_num_of_clauses:                    6498
% 11.49/2.01  prop_preprocess_simplified:             19634
% 11.49/2.01  prop_fo_subsumed:                       383
% 11.49/2.01  prop_solver_time:                       0.
% 11.49/2.01  smt_solver_time:                        0.
% 11.49/2.01  smt_fast_solver_time:                   0.
% 11.49/2.01  prop_fast_solver_time:                  0.
% 11.49/2.01  prop_unsat_core_time:                   0.001
% 11.49/2.01  
% 11.49/2.01  ------ QBF
% 11.49/2.01  
% 11.49/2.01  qbf_q_res:                              0
% 11.49/2.01  qbf_num_tautologies:                    0
% 11.49/2.01  qbf_prep_cycles:                        0
% 11.49/2.01  
% 11.49/2.01  ------ BMC1
% 11.49/2.01  
% 11.49/2.01  bmc1_current_bound:                     -1
% 11.49/2.01  bmc1_last_solved_bound:                 -1
% 11.49/2.01  bmc1_unsat_core_size:                   -1
% 11.49/2.01  bmc1_unsat_core_parents_size:           -1
% 11.49/2.01  bmc1_merge_next_fun:                    0
% 11.49/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.49/2.01  
% 11.49/2.01  ------ Instantiation
% 11.49/2.01  
% 11.49/2.01  inst_num_of_clauses:                    1811
% 11.49/2.01  inst_num_in_passive:                    904
% 11.49/2.01  inst_num_in_active:                     702
% 11.49/2.01  inst_num_in_unprocessed:                205
% 11.49/2.01  inst_num_of_loops:                      830
% 11.49/2.01  inst_num_of_learning_restarts:          0
% 11.49/2.01  inst_num_moves_active_passive:          127
% 11.49/2.01  inst_lit_activity:                      0
% 11.49/2.01  inst_lit_activity_moves:                1
% 11.49/2.01  inst_num_tautologies:                   0
% 11.49/2.01  inst_num_prop_implied:                  0
% 11.49/2.01  inst_num_existing_simplified:           0
% 11.49/2.01  inst_num_eq_res_simplified:             0
% 11.49/2.01  inst_num_child_elim:                    0
% 11.49/2.01  inst_num_of_dismatching_blockings:      682
% 11.49/2.01  inst_num_of_non_proper_insts:           1879
% 11.49/2.01  inst_num_of_duplicates:                 0
% 11.49/2.01  inst_inst_num_from_inst_to_res:         0
% 11.49/2.01  inst_dismatching_checking_time:         0.
% 11.49/2.01  
% 11.49/2.01  ------ Resolution
% 11.49/2.01  
% 11.49/2.01  res_num_of_clauses:                     0
% 11.49/2.01  res_num_in_passive:                     0
% 11.49/2.01  res_num_in_active:                      0
% 11.49/2.01  res_num_of_loops:                       144
% 11.49/2.01  res_forward_subset_subsumed:            12
% 11.49/2.01  res_backward_subset_subsumed:           0
% 11.49/2.01  res_forward_subsumed:                   0
% 11.49/2.01  res_backward_subsumed:                  0
% 11.49/2.01  res_forward_subsumption_resolution:     8
% 11.49/2.01  res_backward_subsumption_resolution:    0
% 11.49/2.01  res_clause_to_clause_subsumption:       4408
% 11.49/2.01  res_orphan_elimination:                 0
% 11.49/2.01  res_tautology_del:                      60
% 11.49/2.01  res_num_eq_res_simplified:              0
% 11.49/2.01  res_num_sel_changes:                    0
% 11.49/2.01  res_moves_from_active_to_pass:          0
% 11.49/2.01  
% 11.49/2.01  ------ Superposition
% 11.49/2.01  
% 11.49/2.01  sup_time_total:                         0.
% 11.49/2.01  sup_time_generating:                    0.
% 11.49/2.01  sup_time_sim_full:                      0.
% 11.49/2.01  sup_time_sim_immed:                     0.
% 11.49/2.01  
% 11.49/2.01  sup_num_of_clauses:                     315
% 11.49/2.01  sup_num_in_active:                      155
% 11.49/2.01  sup_num_in_passive:                     160
% 11.49/2.01  sup_num_of_loops:                       164
% 11.49/2.01  sup_fw_superposition:                   147
% 11.49/2.01  sup_bw_superposition:                   256
% 11.49/2.01  sup_immediate_simplified:               88
% 11.49/2.01  sup_given_eliminated:                   0
% 11.49/2.01  comparisons_done:                       0
% 11.49/2.01  comparisons_avoided:                    18
% 11.49/2.01  
% 11.49/2.01  ------ Simplifications
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  sim_fw_subset_subsumed:                 40
% 11.49/2.01  sim_bw_subset_subsumed:                 15
% 11.49/2.01  sim_fw_subsumed:                        31
% 11.49/2.01  sim_bw_subsumed:                        0
% 11.49/2.01  sim_fw_subsumption_res:                 36
% 11.49/2.01  sim_bw_subsumption_res:                 0
% 11.49/2.01  sim_tautology_del:                      8
% 11.49/2.01  sim_eq_tautology_del:                   15
% 11.49/2.01  sim_eq_res_simp:                        1
% 11.49/2.01  sim_fw_demodulated:                     6
% 11.49/2.01  sim_bw_demodulated:                     5
% 11.49/2.01  sim_light_normalised:                   21
% 11.49/2.01  sim_joinable_taut:                      0
% 11.49/2.01  sim_joinable_simp:                      0
% 11.49/2.01  sim_ac_normalised:                      0
% 11.49/2.01  sim_smt_subsumption:                    0
% 11.49/2.01  
%------------------------------------------------------------------------------
