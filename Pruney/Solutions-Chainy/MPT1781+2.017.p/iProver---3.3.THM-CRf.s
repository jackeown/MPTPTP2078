%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:47 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  461 (114022553 expanded)
%              Number of clauses        :  383 (29689426 expanded)
%              Number of leaves         :   24 (34595628 expanded)
%              Depth                    :   80
%              Number of atoms          : 2047 (1065083098 expanded)
%              Number of equality atoms : 1336 (150039234 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
                & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f42,f41,f40])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f77,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1576,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1568,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1566,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1572,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2041,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1566,c_1572])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_823,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_824,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_826,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_26])).

cnf(c_2048,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2041,c_826])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK2) != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_762,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_1560,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2278,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1560])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_24,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_370,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_371,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | sK3 != k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_454,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_455,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_459,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_33,c_31])).

cnf(c_534,plain,
    ( m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_459])).

cnf(c_535,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_436,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_437,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k4_tmap_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v1_funct_1(k4_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_33,c_31])).

cnf(c_541,plain,
    ( v1_funct_1(k4_tmap_1(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_441])).

cnf(c_542,plain,
    ( v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_21,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_391,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_392,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_33,c_31])).

cnf(c_569,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_396])).

cnf(c_570,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_1167,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1799,plain,
    ( k4_tmap_1(sK1,sK2) != X0
    | sK3 != X0
    | sK3 = k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1800,plain,
    ( k4_tmap_1(sK1,sK2) != k1_xboole_0
    | sK3 = k4_tmap_1(sK1,sK2)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_1563,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_2202,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1563])).

cnf(c_2216,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2202])).

cnf(c_2203,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1566])).

cnf(c_2217,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2203])).

cnf(c_2279,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2278])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK2) != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_570])).

cnf(c_778,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k4_tmap_1(sK1,sK2)
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_1559,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k4_tmap_1(sK1,sK2)
    | k1_xboole_0 = u1_struct_0(sK2)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_2401,plain,
    ( k4_tmap_1(sK1,sK2) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1559])).

cnf(c_2402,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2401])).

cnf(c_2966,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2278,c_371,c_535,c_542,c_570,c_1800,c_2216,c_2217,c_2279,c_2402])).

cnf(c_2042,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1563,c_1572])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_570])).

cnf(c_835,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_837,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_835,c_535])).

cnf(c_2283,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2042,c_837])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1570,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3065,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1570])).

cnf(c_536,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_543,plain,
    ( v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1769,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1977,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_1978,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2171,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2172,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_4662,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3065,c_536,c_543,c_1978,c_2172])).

cnf(c_4663,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4662])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1575,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4675,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4663,c_1575])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_487,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_488,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_492,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_33])).

cnf(c_493,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_492])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(X1)
    | sK1 != sK1
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_493])).

cnf(c_517,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_30])).

cnf(c_522,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_521])).

cnf(c_1564,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_5047,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4675,c_1564])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1567,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4677,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4663,c_1567])).

cnf(c_5300,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5047,c_4677])).

cnf(c_5436,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_5300])).

cnf(c_5600,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_5436])).

cnf(c_5780,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_5600])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1974,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_1975,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_6294,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5780,c_39,c_41,c_1975,c_2172])).

cnf(c_6295,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6294])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1577,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2537,plain,
    ( k1_relat_1(X0) = k1_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1577])).

cnf(c_3470,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_2537])).

cnf(c_4647,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3470,c_536,c_543,c_1978,c_2172])).

cnf(c_4648,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4647])).

cnf(c_6312,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6295,c_4648])).

cnf(c_13776,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_6312])).

cnf(c_14309,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_13776])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_110,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1175,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1774,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_1775,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_1837,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1838,plain,
    ( X0 = sK3
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1837])).

cnf(c_1166,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1852,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1802,plain,
    ( u1_struct_0(sK2) != X0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1908,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_1909,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1966,plain,
    ( k4_tmap_1(sK1,sK2) = k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_2010,plain,
    ( u1_struct_0(sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_2011,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_1997,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_2262,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2263,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_1171,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2405,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_2406,plain,
    ( X0 != sK3
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2405])).

cnf(c_2130,plain,
    ( X0 != X1
    | k4_tmap_1(sK1,sK2) != X1
    | k4_tmap_1(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_2807,plain,
    ( X0 != k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = X0
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_2808,plain,
    ( k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2807])).

cnf(c_1173,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2190,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK2)
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_2839,plain,
    ( X0 != u1_struct_0(sK1)
    | k2_zfmisc_1(u1_struct_0(sK2),X0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2840,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_1172,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1938,plain,
    ( X0 != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_2189,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_5147,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),X0) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_5148,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_5147])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1829,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X0 != k4_tmap_1(sK1,sK2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_1965,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),X0)
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_14575,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_14578,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_14575])).

cnf(c_1824,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_1851,plain,
    ( m1_subset_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_1937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_14588,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_14590,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_14588])).

cnf(c_14800,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14309,c_39,c_26,c_41,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1775,c_1800,c_1838,c_1852,c_1908,c_1909,c_1966,c_1975,c_2011,c_2172,c_2263,c_2406,c_2808,c_2840,c_5148,c_14578,c_14590])).

cnf(c_14811,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_14800])).

cnf(c_2734,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1568])).

cnf(c_4048,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2734,c_536,c_543,c_1978,c_2172])).

cnf(c_4049,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4048])).

cnf(c_4059,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_4049])).

cnf(c_4302,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4059,c_536,c_543,c_1978,c_2172])).

cnf(c_4309,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_4302])).

cnf(c_2733,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1568])).

cnf(c_3677,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2733,c_536,c_543,c_1978,c_2172])).

cnf(c_3678,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3677])).

cnf(c_3688,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_3678])).

cnf(c_3779,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3688,c_536,c_543,c_1978,c_2172])).

cnf(c_3785,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_3779])).

cnf(c_3852,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_1577])).

cnf(c_4474,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4309,c_3852])).

cnf(c_14914,plain,
    ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14811,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_2011,c_2263,c_2808,c_2840,c_4474,c_5148,c_14578,c_14590])).

cnf(c_14915,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_14914])).

cnf(c_14958,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14915,c_1568])).

cnf(c_1790,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | sK3 = k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2500,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1809,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3220,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(sK3,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_4193,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1168,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3215,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | k1_relat_1(k4_tmap_1(sK1,sK2)) != X0
    | k1_relat_1(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_6446,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | k1_relat_1(k4_tmap_1(sK1,sK2)) != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3215])).

cnf(c_13500,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(k4_tmap_1(sK1,sK2)) != k1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6446])).

cnf(c_14949,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14915,c_1568])).

cnf(c_15311,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14949,c_536,c_543,c_1978,c_2172])).

cnf(c_15312,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15311])).

cnf(c_15322,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_15312])).

cnf(c_15335,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15322])).

cnf(c_5435,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4309,c_5300])).

cnf(c_5478,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5435,c_39,c_41,c_1975,c_2172])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1569,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2732,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1569])).

cnf(c_4232,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2732,c_536,c_543,c_1978,c_2172])).

cnf(c_4233,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4232])).

cnf(c_5490,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5478,c_4233])).

cnf(c_12636,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5490,c_39,c_41,c_1975,c_2172])).

cnf(c_12648,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_12636])).

cnf(c_12687,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_12648])).

cnf(c_13340,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12687,c_39,c_41,c_1975,c_2172])).

cnf(c_13341,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13340])).

cnf(c_13356,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_13341])).

cnf(c_2023,plain,
    ( k4_tmap_1(sK1,sK2) != sK3
    | sK3 = k4_tmap_1(sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2058,plain,
    ( r1_tarski(X0,k4_tmap_1(sK1,sK2))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0,k4_tmap_1(sK1,sK2))) != k1_funct_1(X0,sK0(X0,k4_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3138,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_5487,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5478,c_1577])).

cnf(c_5515,plain,
    ( ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5487])).

cnf(c_13412,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13356])).

cnf(c_15768,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13356,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,c_5148,c_5515,c_13412,c_14578,c_14590,c_15335])).

cnf(c_15770,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15768])).

cnf(c_15772,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15768,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,c_5148,c_5515,c_13412,c_14578,c_14590,c_15335])).

cnf(c_15773,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15772])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_409,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_410,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_414,plain,
    ( v2_struct_0(X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_33,c_31])).

cnf(c_415,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(X0)
    | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_548,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(X1)
    | k1_funct_1(k4_tmap_1(sK1,X1),X0) = X0
    | sK1 != sK1
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_415])).

cnf(c_549,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_30])).

cnf(c_554,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_1561,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_4676,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4663,c_1561])).

cnf(c_5299,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5047,c_4676])).

cnf(c_5639,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4309,c_5299])).

cnf(c_11523,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5639,c_39,c_41,c_1975,c_2172])).

cnf(c_11543,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11523,c_4233])).

cnf(c_12781,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11543,c_39,c_41,c_1975,c_2172])).

cnf(c_12793,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_12781])).

cnf(c_12832,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_12793])).

cnf(c_14108,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12832,c_39,c_41,c_1975,c_2172])).

cnf(c_14109,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14108])).

cnf(c_14124,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_14109])).

cnf(c_11535,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11523,c_1577])).

cnf(c_11688,plain,
    ( ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11535])).

cnf(c_14180,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14124])).

cnf(c_15900,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14124,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,c_5148,c_11688,c_14180,c_14578,c_14590,c_15335])).

cnf(c_15902,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15900])).

cnf(c_15904,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15900,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,c_5148,c_11688,c_14180,c_14578,c_14590,c_15335])).

cnf(c_15905,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15904])).

cnf(c_1571,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_15908,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15905,c_1571])).

cnf(c_15909,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15908])).

cnf(c_15443,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15322,c_536,c_543,c_1978,c_2172])).

cnf(c_3066,plain,
    ( m1_subset_1(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1575])).

cnf(c_2980,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_1564])).

cnf(c_3637,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_2980])).

cnf(c_4115,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3637,c_39,c_41,c_1975,c_2172])).

cnf(c_4116,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4115])).

cnf(c_2982,plain,
    ( k1_funct_1(sK3,X0) = X0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_1567])).

cnf(c_3234,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_2982])).

cnf(c_3421,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3234,c_39,c_41,c_1975,c_2172])).

cnf(c_3422,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3421])).

cnf(c_4128,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4116,c_3422])).

cnf(c_15466,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15443,c_4128])).

cnf(c_2505,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2500])).

cnf(c_3221,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3220])).

cnf(c_14945,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14915,c_4128])).

cnf(c_15564,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15466,c_39,c_41,c_536,c_543,c_1975,c_1978,c_2172,c_2505,c_3221,c_14945])).

cnf(c_15575,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15564,c_1577])).

cnf(c_4153,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_4128])).

cnf(c_11700,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4153,c_536,c_543,c_1978,c_2172])).

cnf(c_11712,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11700,c_1577])).

cnf(c_11886,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11712])).

cnf(c_16157,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15575,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,c_1977,c_2011,c_2023,c_2171,c_2263,c_2500,c_2808,c_2840,c_3138,c_3220,c_4193,c_4474,c_5148,c_5515,c_11886,c_13412,c_13500,c_14578,c_14590,c_15335,c_15909])).

cnf(c_16158,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_16157])).

cnf(c_2977,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_1561])).

cnf(c_3318,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_2977])).

cnf(c_5988,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3318,c_39,c_41,c_1975,c_2172,c_3637])).

cnf(c_5989,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5988])).

cnf(c_15464,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15443,c_5989])).

cnf(c_14938,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14915,c_5989])).

cnf(c_15700,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15464,c_39,c_41,c_536,c_543,c_1975,c_1978,c_2172,c_2505,c_3221,c_14938])).

cnf(c_15711,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15700,c_1577])).

cnf(c_6002,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_5989])).

cnf(c_12060,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6002,c_536,c_543,c_1978,c_2172])).

cnf(c_12072,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12060,c_1577])).

cnf(c_12255,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12072])).

cnf(c_16299,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15711,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,c_1977,c_2011,c_2023,c_2171,c_2263,c_2500,c_2808,c_2840,c_3138,c_3220,c_4193,c_4474,c_5148,c_5515,c_12255,c_13412,c_13500,c_14578,c_14590,c_15335,c_15909])).

cnf(c_16300,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_16299])).

cnf(c_16303,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16300,c_1571])).

cnf(c_16304,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16303])).

cnf(c_16306,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14958,c_28,c_26,c_371,c_535,c_542,c_570,c_1790,c_1974,c_1977,c_2171,c_2500,c_3220,c_4193,c_13500,c_14915,c_15335,c_15773,c_15909,c_16158,c_16304])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_570])).

cnf(c_811,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_1557,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_16418,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1557])).

cnf(c_16468,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16418])).

cnf(c_16419,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_16306,c_2042])).

cnf(c_16469,plain,
    ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16468,c_16419])).

cnf(c_16428,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1563])).

cnf(c_16472,plain,
    ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16469,c_16428])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_798,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_1558,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_16423,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1558])).

cnf(c_16457,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16423])).

cnf(c_16425,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_16306,c_2041])).

cnf(c_16458,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16457,c_16425])).

cnf(c_16430,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1566])).

cnf(c_16461,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16458,c_16430])).

cnf(c_17062,plain,
    ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16461,c_1570])).

cnf(c_17197,plain,
    ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17062,c_16461])).

cnf(c_19069,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17197,c_39,c_41,c_1975,c_2172])).

cnf(c_19070,plain,
    ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19069])).

cnf(c_16427,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1564])).

cnf(c_16424,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1561])).

cnf(c_17712,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16427,c_16424])).

cnf(c_18517,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17712,c_1575])).

cnf(c_19081,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19070,c_18517])).

cnf(c_20943,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16472,c_19081])).

cnf(c_105,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_107,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_22319,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20943,c_107,c_536,c_543,c_1978,c_2172])).

cnf(c_22320,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_22319])).

cnf(c_17787,plain,
    ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16472,c_1570])).

cnf(c_17922,plain,
    ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17787,c_16472])).

cnf(c_20961,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17922,c_536,c_543,c_1978,c_2172])).

cnf(c_20962,plain,
    ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20961])).

cnf(c_20973,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20962,c_18517])).

cnf(c_21664,plain,
    ( k4_tmap_1(sK1,sK2) = X0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20973,c_1577])).

cnf(c_22330,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22320,c_21664])).

cnf(c_22398,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22330,c_16461])).

cnf(c_16429,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16306,c_1567])).

cnf(c_17459,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16427,c_16429])).

cnf(c_17489,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17459,c_1575])).

cnf(c_20974,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20962,c_17489])).

cnf(c_21147,plain,
    ( k4_tmap_1(sK1,sK2) = X0
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20974,c_1577])).

cnf(c_22331,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22320,c_21147])).

cnf(c_22385,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22331,c_16461])).

cnf(c_22441,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22385])).

cnf(c_22444,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22385,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,c_1975,c_2023,c_2172])).

cnf(c_22445,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(renaming,[status(thm)],[c_22444])).

cnf(c_22327,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22320,c_1577])).

cnf(c_22538,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22327,c_371,c_535,c_542,c_570,c_1852,c_2023])).

cnf(c_22546,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20973,c_22538])).

cnf(c_22553,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22546,c_16461])).

cnf(c_22561,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22553,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,c_1975,c_2023,c_2172,c_22398])).

cnf(c_22562,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_22561])).

cnf(c_22565,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22562,c_1571])).

cnf(c_22566,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22565,c_16461,c_16472])).

cnf(c_22918,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22398,c_39,c_41,c_107,c_536,c_543,c_1975,c_1978,c_2172,c_22445,c_22538,c_22566])).

cnf(c_22921,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22918,c_1571])).

cnf(c_19082,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19070,c_17489])).

cnf(c_20836,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16472,c_19082])).

cnf(c_22078,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20836,c_107,c_536,c_543,c_1978,c_2172])).

cnf(c_22079,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_22078])).

cnf(c_22089,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22079,c_21664])).

cnf(c_22157,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22089,c_16461])).

cnf(c_22258,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22157,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,c_1975,c_2023,c_2172])).

cnf(c_22259,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_22258])).

cnf(c_22262,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22259,c_1571])).

cnf(c_22263,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22262,c_16461,c_16472])).

cnf(c_22086,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22079,c_1577])).

cnf(c_22196,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22086])).

cnf(c_22090,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22079,c_21147])).

cnf(c_22144,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22090,c_16461])).

cnf(c_22264,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22263])).

cnf(c_22266,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22263,c_28,c_39,c_26,c_41,c_106,c_107,c_371,c_535,c_542,c_570,c_1852,c_1974,c_1975,c_1977,c_2023,c_2171,c_2172,c_22196,c_22144,c_22264])).

cnf(c_22922,plain,
    ( sK0(sK3,k4_tmap_1(sK1,sK2)) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22921,c_16461,c_16472,c_22266])).

cnf(c_22923,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_22922])).

cnf(c_22926,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22923,c_39,c_41,c_107,c_536,c_543,c_1975,c_1978,c_2172])).

cnf(c_22936,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22926,c_21664])).

cnf(c_22995,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22936,c_16461])).

cnf(c_23198,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22995,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,c_1975,c_2023,c_2172])).

cnf(c_23201,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_23198,c_1571])).

cnf(c_22937,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22926,c_21147])).

cnf(c_22984,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22937,c_16461])).

cnf(c_23194,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22984,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,c_1975,c_2023,c_2172])).

cnf(c_23202,plain,
    ( sK0(k4_tmap_1(sK1,sK2),sK3) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23201,c_16461,c_16472,c_23194])).

cnf(c_23203,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23202])).

cnf(c_18491,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_18492,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18491])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23203,c_22923,c_18492,c_2172,c_2023,c_1978,c_1975,c_1852,c_570,c_543,c_542,c_536,c_535,c_371,c_107,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.32/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/1.48  
% 7.32/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.48  
% 7.32/1.48  ------  iProver source info
% 7.32/1.48  
% 7.32/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.48  git: non_committed_changes: false
% 7.32/1.48  git: last_make_outside_of_git: false
% 7.32/1.48  
% 7.32/1.48  ------ 
% 7.32/1.48  
% 7.32/1.48  ------ Input Options
% 7.32/1.48  
% 7.32/1.48  --out_options                           all
% 7.32/1.48  --tptp_safe_out                         true
% 7.32/1.48  --problem_path                          ""
% 7.32/1.48  --include_path                          ""
% 7.32/1.48  --clausifier                            res/vclausify_rel
% 7.32/1.48  --clausifier_options                    --mode clausify
% 7.32/1.48  --stdin                                 false
% 7.32/1.48  --stats_out                             all
% 7.32/1.48  
% 7.32/1.48  ------ General Options
% 7.32/1.48  
% 7.32/1.48  --fof                                   false
% 7.32/1.48  --time_out_real                         305.
% 7.32/1.48  --time_out_virtual                      -1.
% 7.32/1.48  --symbol_type_check                     false
% 7.32/1.48  --clausify_out                          false
% 7.32/1.48  --sig_cnt_out                           false
% 7.32/1.48  --trig_cnt_out                          false
% 7.32/1.48  --trig_cnt_out_tolerance                1.
% 7.32/1.48  --trig_cnt_out_sk_spl                   false
% 7.32/1.48  --abstr_cl_out                          false
% 7.32/1.48  
% 7.32/1.48  ------ Global Options
% 7.32/1.48  
% 7.32/1.48  --schedule                              default
% 7.32/1.48  --add_important_lit                     false
% 7.32/1.48  --prop_solver_per_cl                    1000
% 7.32/1.48  --min_unsat_core                        false
% 7.32/1.48  --soft_assumptions                      false
% 7.32/1.48  --soft_lemma_size                       3
% 7.32/1.48  --prop_impl_unit_size                   0
% 7.32/1.48  --prop_impl_unit                        []
% 7.32/1.48  --share_sel_clauses                     true
% 7.32/1.48  --reset_solvers                         false
% 7.32/1.48  --bc_imp_inh                            [conj_cone]
% 7.32/1.48  --conj_cone_tolerance                   3.
% 7.32/1.48  --extra_neg_conj                        none
% 7.32/1.48  --large_theory_mode                     true
% 7.32/1.48  --prolific_symb_bound                   200
% 7.32/1.48  --lt_threshold                          2000
% 7.32/1.48  --clause_weak_htbl                      true
% 7.32/1.48  --gc_record_bc_elim                     false
% 7.32/1.48  
% 7.32/1.48  ------ Preprocessing Options
% 7.32/1.48  
% 7.32/1.48  --preprocessing_flag                    true
% 7.32/1.48  --time_out_prep_mult                    0.1
% 7.32/1.48  --splitting_mode                        input
% 7.32/1.48  --splitting_grd                         true
% 7.32/1.48  --splitting_cvd                         false
% 7.32/1.48  --splitting_cvd_svl                     false
% 7.32/1.48  --splitting_nvd                         32
% 7.32/1.48  --sub_typing                            true
% 7.32/1.48  --prep_gs_sim                           true
% 7.32/1.48  --prep_unflatten                        true
% 7.32/1.48  --prep_res_sim                          true
% 7.32/1.48  --prep_upred                            true
% 7.32/1.48  --prep_sem_filter                       exhaustive
% 7.32/1.48  --prep_sem_filter_out                   false
% 7.32/1.48  --pred_elim                             true
% 7.32/1.48  --res_sim_input                         true
% 7.32/1.48  --eq_ax_congr_red                       true
% 7.32/1.48  --pure_diseq_elim                       true
% 7.32/1.48  --brand_transform                       false
% 7.32/1.48  --non_eq_to_eq                          false
% 7.32/1.48  --prep_def_merge                        true
% 7.32/1.48  --prep_def_merge_prop_impl              false
% 7.32/1.48  --prep_def_merge_mbd                    true
% 7.32/1.48  --prep_def_merge_tr_red                 false
% 7.32/1.48  --prep_def_merge_tr_cl                  false
% 7.32/1.48  --smt_preprocessing                     true
% 7.32/1.48  --smt_ac_axioms                         fast
% 7.32/1.48  --preprocessed_out                      false
% 7.32/1.48  --preprocessed_stats                    false
% 7.32/1.48  
% 7.32/1.48  ------ Abstraction refinement Options
% 7.32/1.48  
% 7.32/1.48  --abstr_ref                             []
% 7.32/1.48  --abstr_ref_prep                        false
% 7.32/1.48  --abstr_ref_until_sat                   false
% 7.32/1.48  --abstr_ref_sig_restrict                funpre
% 7.32/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.48  --abstr_ref_under                       []
% 7.32/1.48  
% 7.32/1.48  ------ SAT Options
% 7.32/1.48  
% 7.32/1.48  --sat_mode                              false
% 7.32/1.48  --sat_fm_restart_options                ""
% 7.32/1.48  --sat_gr_def                            false
% 7.32/1.48  --sat_epr_types                         true
% 7.32/1.48  --sat_non_cyclic_types                  false
% 7.32/1.48  --sat_finite_models                     false
% 7.32/1.48  --sat_fm_lemmas                         false
% 7.32/1.48  --sat_fm_prep                           false
% 7.32/1.48  --sat_fm_uc_incr                        true
% 7.32/1.48  --sat_out_model                         small
% 7.32/1.48  --sat_out_clauses                       false
% 7.32/1.48  
% 7.32/1.48  ------ QBF Options
% 7.32/1.48  
% 7.32/1.48  --qbf_mode                              false
% 7.32/1.48  --qbf_elim_univ                         false
% 7.32/1.48  --qbf_dom_inst                          none
% 7.32/1.48  --qbf_dom_pre_inst                      false
% 7.32/1.48  --qbf_sk_in                             false
% 7.32/1.48  --qbf_pred_elim                         true
% 7.32/1.48  --qbf_split                             512
% 7.32/1.48  
% 7.32/1.48  ------ BMC1 Options
% 7.32/1.48  
% 7.32/1.48  --bmc1_incremental                      false
% 7.32/1.48  --bmc1_axioms                           reachable_all
% 7.32/1.48  --bmc1_min_bound                        0
% 7.32/1.48  --bmc1_max_bound                        -1
% 7.32/1.48  --bmc1_max_bound_default                -1
% 7.32/1.48  --bmc1_symbol_reachability              true
% 7.32/1.48  --bmc1_property_lemmas                  false
% 7.32/1.48  --bmc1_k_induction                      false
% 7.32/1.48  --bmc1_non_equiv_states                 false
% 7.32/1.48  --bmc1_deadlock                         false
% 7.32/1.48  --bmc1_ucm                              false
% 7.32/1.48  --bmc1_add_unsat_core                   none
% 7.32/1.48  --bmc1_unsat_core_children              false
% 7.32/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.48  --bmc1_out_stat                         full
% 7.32/1.48  --bmc1_ground_init                      false
% 7.32/1.48  --bmc1_pre_inst_next_state              false
% 7.32/1.48  --bmc1_pre_inst_state                   false
% 7.32/1.48  --bmc1_pre_inst_reach_state             false
% 7.32/1.48  --bmc1_out_unsat_core                   false
% 7.32/1.48  --bmc1_aig_witness_out                  false
% 7.32/1.48  --bmc1_verbose                          false
% 7.32/1.48  --bmc1_dump_clauses_tptp                false
% 7.32/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.48  --bmc1_dump_file                        -
% 7.32/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.48  --bmc1_ucm_extend_mode                  1
% 7.32/1.48  --bmc1_ucm_init_mode                    2
% 7.32/1.48  --bmc1_ucm_cone_mode                    none
% 7.32/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.48  --bmc1_ucm_relax_model                  4
% 7.32/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.48  --bmc1_ucm_layered_model                none
% 7.32/1.48  --bmc1_ucm_max_lemma_size               10
% 7.32/1.48  
% 7.32/1.48  ------ AIG Options
% 7.32/1.48  
% 7.32/1.48  --aig_mode                              false
% 7.32/1.48  
% 7.32/1.48  ------ Instantiation Options
% 7.32/1.48  
% 7.32/1.48  --instantiation_flag                    true
% 7.32/1.48  --inst_sos_flag                         false
% 7.32/1.48  --inst_sos_phase                        true
% 7.32/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.48  --inst_lit_sel_side                     num_symb
% 7.32/1.48  --inst_solver_per_active                1400
% 7.32/1.48  --inst_solver_calls_frac                1.
% 7.32/1.48  --inst_passive_queue_type               priority_queues
% 7.32/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.48  --inst_passive_queues_freq              [25;2]
% 7.32/1.48  --inst_dismatching                      true
% 7.32/1.48  --inst_eager_unprocessed_to_passive     true
% 7.32/1.48  --inst_prop_sim_given                   true
% 7.32/1.48  --inst_prop_sim_new                     false
% 7.32/1.48  --inst_subs_new                         false
% 7.32/1.48  --inst_eq_res_simp                      false
% 7.32/1.48  --inst_subs_given                       false
% 7.32/1.48  --inst_orphan_elimination               true
% 7.32/1.48  --inst_learning_loop_flag               true
% 7.32/1.48  --inst_learning_start                   3000
% 7.32/1.48  --inst_learning_factor                  2
% 7.32/1.48  --inst_start_prop_sim_after_learn       3
% 7.32/1.48  --inst_sel_renew                        solver
% 7.32/1.48  --inst_lit_activity_flag                true
% 7.32/1.48  --inst_restr_to_given                   false
% 7.32/1.48  --inst_activity_threshold               500
% 7.32/1.48  --inst_out_proof                        true
% 7.32/1.48  
% 7.32/1.48  ------ Resolution Options
% 7.32/1.48  
% 7.32/1.48  --resolution_flag                       true
% 7.32/1.48  --res_lit_sel                           adaptive
% 7.32/1.48  --res_lit_sel_side                      none
% 7.32/1.48  --res_ordering                          kbo
% 7.32/1.48  --res_to_prop_solver                    active
% 7.32/1.48  --res_prop_simpl_new                    false
% 7.32/1.48  --res_prop_simpl_given                  true
% 7.32/1.48  --res_passive_queue_type                priority_queues
% 7.32/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.48  --res_passive_queues_freq               [15;5]
% 7.32/1.48  --res_forward_subs                      full
% 7.32/1.48  --res_backward_subs                     full
% 7.32/1.48  --res_forward_subs_resolution           true
% 7.32/1.48  --res_backward_subs_resolution          true
% 7.32/1.48  --res_orphan_elimination                true
% 7.32/1.48  --res_time_limit                        2.
% 7.32/1.48  --res_out_proof                         true
% 7.32/1.48  
% 7.32/1.48  ------ Superposition Options
% 7.32/1.48  
% 7.32/1.48  --superposition_flag                    true
% 7.32/1.48  --sup_passive_queue_type                priority_queues
% 7.32/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.48  --demod_completeness_check              fast
% 7.32/1.48  --demod_use_ground                      true
% 7.32/1.48  --sup_to_prop_solver                    passive
% 7.32/1.48  --sup_prop_simpl_new                    true
% 7.32/1.48  --sup_prop_simpl_given                  true
% 7.32/1.48  --sup_fun_splitting                     false
% 7.32/1.48  --sup_smt_interval                      50000
% 7.32/1.48  
% 7.32/1.48  ------ Superposition Simplification Setup
% 7.32/1.48  
% 7.32/1.48  --sup_indices_passive                   []
% 7.32/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.48  --sup_full_bw                           [BwDemod]
% 7.32/1.48  --sup_immed_triv                        [TrivRules]
% 7.32/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.48  --sup_immed_bw_main                     []
% 7.32/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.48  
% 7.32/1.48  ------ Combination Options
% 7.32/1.48  
% 7.32/1.48  --comb_res_mult                         3
% 7.32/1.48  --comb_sup_mult                         2
% 7.32/1.48  --comb_inst_mult                        10
% 7.32/1.48  
% 7.32/1.48  ------ Debug Options
% 7.32/1.48  
% 7.32/1.48  --dbg_backtrace                         false
% 7.32/1.48  --dbg_dump_prop_clauses                 false
% 7.32/1.48  --dbg_dump_prop_clauses_file            -
% 7.32/1.48  --dbg_out_stat                          false
% 7.32/1.48  ------ Parsing...
% 7.32/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.48  
% 7.32/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.32/1.48  
% 7.32/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.48  
% 7.32/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.48  ------ Proving...
% 7.32/1.48  ------ Problem Properties 
% 7.32/1.48  
% 7.32/1.48  
% 7.32/1.48  clauses                                 24
% 7.32/1.48  conjectures                             3
% 7.32/1.48  EPR                                     4
% 7.32/1.48  Horn                                    19
% 7.32/1.48  unary                                   7
% 7.32/1.48  binary                                  5
% 7.32/1.48  lits                                    70
% 7.32/1.48  lits eq                                 21
% 7.32/1.48  fd_pure                                 0
% 7.32/1.48  fd_pseudo                               0
% 7.32/1.48  fd_cond                                 0
% 7.32/1.48  fd_pseudo_cond                          1
% 7.32/1.48  AC symbols                              0
% 7.32/1.48  
% 7.32/1.48  ------ Schedule dynamic 5 is on 
% 7.32/1.48  
% 7.32/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.48  
% 7.32/1.48  
% 7.32/1.48  ------ 
% 7.32/1.48  Current options:
% 7.32/1.48  ------ 
% 7.32/1.48  
% 7.32/1.48  ------ Input Options
% 7.32/1.48  
% 7.32/1.48  --out_options                           all
% 7.32/1.48  --tptp_safe_out                         true
% 7.32/1.48  --problem_path                          ""
% 7.32/1.48  --include_path                          ""
% 7.32/1.48  --clausifier                            res/vclausify_rel
% 7.32/1.48  --clausifier_options                    --mode clausify
% 7.32/1.48  --stdin                                 false
% 7.32/1.48  --stats_out                             all
% 7.32/1.48  
% 7.32/1.48  ------ General Options
% 7.32/1.48  
% 7.32/1.48  --fof                                   false
% 7.32/1.48  --time_out_real                         305.
% 7.32/1.48  --time_out_virtual                      -1.
% 7.32/1.48  --symbol_type_check                     false
% 7.32/1.48  --clausify_out                          false
% 7.32/1.48  --sig_cnt_out                           false
% 7.32/1.48  --trig_cnt_out                          false
% 7.32/1.48  --trig_cnt_out_tolerance                1.
% 7.32/1.48  --trig_cnt_out_sk_spl                   false
% 7.32/1.48  --abstr_cl_out                          false
% 7.32/1.48  
% 7.32/1.48  ------ Global Options
% 7.32/1.48  
% 7.32/1.48  --schedule                              default
% 7.32/1.48  --add_important_lit                     false
% 7.32/1.48  --prop_solver_per_cl                    1000
% 7.32/1.48  --min_unsat_core                        false
% 7.32/1.48  --soft_assumptions                      false
% 7.32/1.48  --soft_lemma_size                       3
% 7.32/1.48  --prop_impl_unit_size                   0
% 7.32/1.48  --prop_impl_unit                        []
% 7.32/1.48  --share_sel_clauses                     true
% 7.32/1.48  --reset_solvers                         false
% 7.32/1.48  --bc_imp_inh                            [conj_cone]
% 7.32/1.48  --conj_cone_tolerance                   3.
% 7.32/1.48  --extra_neg_conj                        none
% 7.32/1.48  --large_theory_mode                     true
% 7.32/1.48  --prolific_symb_bound                   200
% 7.32/1.48  --lt_threshold                          2000
% 7.32/1.48  --clause_weak_htbl                      true
% 7.32/1.48  --gc_record_bc_elim                     false
% 7.32/1.48  
% 7.32/1.48  ------ Preprocessing Options
% 7.32/1.48  
% 7.32/1.48  --preprocessing_flag                    true
% 7.32/1.48  --time_out_prep_mult                    0.1
% 7.32/1.48  --splitting_mode                        input
% 7.32/1.48  --splitting_grd                         true
% 7.32/1.48  --splitting_cvd                         false
% 7.32/1.48  --splitting_cvd_svl                     false
% 7.32/1.48  --splitting_nvd                         32
% 7.32/1.48  --sub_typing                            true
% 7.32/1.48  --prep_gs_sim                           true
% 7.32/1.48  --prep_unflatten                        true
% 7.32/1.48  --prep_res_sim                          true
% 7.32/1.48  --prep_upred                            true
% 7.32/1.48  --prep_sem_filter                       exhaustive
% 7.32/1.48  --prep_sem_filter_out                   false
% 7.32/1.48  --pred_elim                             true
% 7.32/1.48  --res_sim_input                         true
% 7.32/1.48  --eq_ax_congr_red                       true
% 7.32/1.48  --pure_diseq_elim                       true
% 7.32/1.48  --brand_transform                       false
% 7.32/1.48  --non_eq_to_eq                          false
% 7.32/1.48  --prep_def_merge                        true
% 7.32/1.48  --prep_def_merge_prop_impl              false
% 7.32/1.48  --prep_def_merge_mbd                    true
% 7.32/1.48  --prep_def_merge_tr_red                 false
% 7.32/1.48  --prep_def_merge_tr_cl                  false
% 7.32/1.48  --smt_preprocessing                     true
% 7.32/1.48  --smt_ac_axioms                         fast
% 7.32/1.48  --preprocessed_out                      false
% 7.32/1.48  --preprocessed_stats                    false
% 7.32/1.48  
% 7.32/1.48  ------ Abstraction refinement Options
% 7.32/1.48  
% 7.32/1.48  --abstr_ref                             []
% 7.32/1.48  --abstr_ref_prep                        false
% 7.32/1.48  --abstr_ref_until_sat                   false
% 7.32/1.48  --abstr_ref_sig_restrict                funpre
% 7.32/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.48  --abstr_ref_under                       []
% 7.32/1.48  
% 7.32/1.48  ------ SAT Options
% 7.32/1.48  
% 7.32/1.48  --sat_mode                              false
% 7.32/1.48  --sat_fm_restart_options                ""
% 7.32/1.48  --sat_gr_def                            false
% 7.32/1.48  --sat_epr_types                         true
% 7.32/1.48  --sat_non_cyclic_types                  false
% 7.32/1.48  --sat_finite_models                     false
% 7.32/1.48  --sat_fm_lemmas                         false
% 7.32/1.48  --sat_fm_prep                           false
% 7.32/1.48  --sat_fm_uc_incr                        true
% 7.32/1.48  --sat_out_model                         small
% 7.32/1.48  --sat_out_clauses                       false
% 7.32/1.48  
% 7.32/1.48  ------ QBF Options
% 7.32/1.48  
% 7.32/1.48  --qbf_mode                              false
% 7.32/1.48  --qbf_elim_univ                         false
% 7.32/1.48  --qbf_dom_inst                          none
% 7.32/1.48  --qbf_dom_pre_inst                      false
% 7.32/1.48  --qbf_sk_in                             false
% 7.32/1.48  --qbf_pred_elim                         true
% 7.32/1.48  --qbf_split                             512
% 7.32/1.48  
% 7.32/1.48  ------ BMC1 Options
% 7.32/1.48  
% 7.32/1.48  --bmc1_incremental                      false
% 7.32/1.48  --bmc1_axioms                           reachable_all
% 7.32/1.48  --bmc1_min_bound                        0
% 7.32/1.48  --bmc1_max_bound                        -1
% 7.32/1.48  --bmc1_max_bound_default                -1
% 7.32/1.48  --bmc1_symbol_reachability              true
% 7.32/1.48  --bmc1_property_lemmas                  false
% 7.32/1.48  --bmc1_k_induction                      false
% 7.32/1.48  --bmc1_non_equiv_states                 false
% 7.32/1.48  --bmc1_deadlock                         false
% 7.32/1.48  --bmc1_ucm                              false
% 7.32/1.48  --bmc1_add_unsat_core                   none
% 7.32/1.48  --bmc1_unsat_core_children              false
% 7.32/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.48  --bmc1_out_stat                         full
% 7.32/1.48  --bmc1_ground_init                      false
% 7.32/1.48  --bmc1_pre_inst_next_state              false
% 7.32/1.48  --bmc1_pre_inst_state                   false
% 7.32/1.48  --bmc1_pre_inst_reach_state             false
% 7.32/1.48  --bmc1_out_unsat_core                   false
% 7.32/1.48  --bmc1_aig_witness_out                  false
% 7.32/1.48  --bmc1_verbose                          false
% 7.32/1.48  --bmc1_dump_clauses_tptp                false
% 7.32/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.48  --bmc1_dump_file                        -
% 7.32/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.48  --bmc1_ucm_extend_mode                  1
% 7.32/1.48  --bmc1_ucm_init_mode                    2
% 7.32/1.48  --bmc1_ucm_cone_mode                    none
% 7.32/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.48  --bmc1_ucm_relax_model                  4
% 7.32/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.48  --bmc1_ucm_layered_model                none
% 7.32/1.48  --bmc1_ucm_max_lemma_size               10
% 7.32/1.48  
% 7.32/1.48  ------ AIG Options
% 7.32/1.48  
% 7.32/1.48  --aig_mode                              false
% 7.32/1.48  
% 7.32/1.48  ------ Instantiation Options
% 7.32/1.48  
% 7.32/1.48  --instantiation_flag                    true
% 7.32/1.48  --inst_sos_flag                         false
% 7.32/1.48  --inst_sos_phase                        true
% 7.32/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.48  --inst_lit_sel_side                     none
% 7.32/1.48  --inst_solver_per_active                1400
% 7.32/1.48  --inst_solver_calls_frac                1.
% 7.32/1.48  --inst_passive_queue_type               priority_queues
% 7.32/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.48  --inst_passive_queues_freq              [25;2]
% 7.32/1.48  --inst_dismatching                      true
% 7.32/1.48  --inst_eager_unprocessed_to_passive     true
% 7.32/1.48  --inst_prop_sim_given                   true
% 7.32/1.48  --inst_prop_sim_new                     false
% 7.32/1.48  --inst_subs_new                         false
% 7.32/1.48  --inst_eq_res_simp                      false
% 7.32/1.48  --inst_subs_given                       false
% 7.32/1.48  --inst_orphan_elimination               true
% 7.32/1.48  --inst_learning_loop_flag               true
% 7.32/1.48  --inst_learning_start                   3000
% 7.32/1.48  --inst_learning_factor                  2
% 7.32/1.48  --inst_start_prop_sim_after_learn       3
% 7.32/1.48  --inst_sel_renew                        solver
% 7.32/1.48  --inst_lit_activity_flag                true
% 7.32/1.48  --inst_restr_to_given                   false
% 7.32/1.48  --inst_activity_threshold               500
% 7.32/1.48  --inst_out_proof                        true
% 7.32/1.48  
% 7.32/1.48  ------ Resolution Options
% 7.32/1.48  
% 7.32/1.48  --resolution_flag                       false
% 7.32/1.48  --res_lit_sel                           adaptive
% 7.32/1.48  --res_lit_sel_side                      none
% 7.32/1.48  --res_ordering                          kbo
% 7.32/1.48  --res_to_prop_solver                    active
% 7.32/1.48  --res_prop_simpl_new                    false
% 7.32/1.48  --res_prop_simpl_given                  true
% 7.32/1.48  --res_passive_queue_type                priority_queues
% 7.32/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.48  --res_passive_queues_freq               [15;5]
% 7.32/1.48  --res_forward_subs                      full
% 7.32/1.48  --res_backward_subs                     full
% 7.32/1.48  --res_forward_subs_resolution           true
% 7.32/1.48  --res_backward_subs_resolution          true
% 7.32/1.48  --res_orphan_elimination                true
% 7.32/1.48  --res_time_limit                        2.
% 7.32/1.48  --res_out_proof                         true
% 7.32/1.48  
% 7.32/1.48  ------ Superposition Options
% 7.32/1.48  
% 7.32/1.48  --superposition_flag                    true
% 7.32/1.48  --sup_passive_queue_type                priority_queues
% 7.32/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.48  --demod_completeness_check              fast
% 7.32/1.48  --demod_use_ground                      true
% 7.32/1.48  --sup_to_prop_solver                    passive
% 7.32/1.48  --sup_prop_simpl_new                    true
% 7.32/1.48  --sup_prop_simpl_given                  true
% 7.32/1.48  --sup_fun_splitting                     false
% 7.32/1.48  --sup_smt_interval                      50000
% 7.32/1.48  
% 7.32/1.48  ------ Superposition Simplification Setup
% 7.32/1.48  
% 7.32/1.48  --sup_indices_passive                   []
% 7.32/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.48  --sup_full_bw                           [BwDemod]
% 7.32/1.48  --sup_immed_triv                        [TrivRules]
% 7.32/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.48  --sup_immed_bw_main                     []
% 7.32/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.48  
% 7.32/1.48  ------ Combination Options
% 7.32/1.48  
% 7.32/1.48  --comb_res_mult                         3
% 7.32/1.48  --comb_sup_mult                         2
% 7.32/1.48  --comb_inst_mult                        10
% 7.32/1.48  
% 7.32/1.48  ------ Debug Options
% 7.32/1.48  
% 7.32/1.48  --dbg_backtrace                         false
% 7.32/1.48  --dbg_dump_prop_clauses                 false
% 7.32/1.48  --dbg_dump_prop_clauses_file            -
% 7.32/1.48  --dbg_out_stat                          false
% 7.32/1.48  
% 7.32/1.48  
% 7.32/1.48  
% 7.32/1.48  
% 7.32/1.48  ------ Proving...
% 7.32/1.48  
% 7.32/1.48  
% 7.32/1.48  % SZS status Theorem for theBenchmark.p
% 7.32/1.48  
% 7.32/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.48  
% 7.32/1.48  fof(f1,axiom,(
% 7.32/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f31,plain,(
% 7.32/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.32/1.48    inference(nnf_transformation,[],[f1])).
% 7.32/1.48  
% 7.32/1.48  fof(f32,plain,(
% 7.32/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.32/1.48    inference(flattening,[],[f31])).
% 7.32/1.48  
% 7.32/1.48  fof(f45,plain,(
% 7.32/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.32/1.48    inference(cnf_transformation,[],[f32])).
% 7.32/1.48  
% 7.32/1.48  fof(f78,plain,(
% 7.32/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.32/1.48    inference(equality_resolution,[],[f45])).
% 7.32/1.48  
% 7.32/1.48  fof(f8,axiom,(
% 7.32/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f21,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.32/1.48    inference(ennf_transformation,[],[f8])).
% 7.32/1.48  
% 7.32/1.48  fof(f22,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.48    inference(flattening,[],[f21])).
% 7.32/1.48  
% 7.32/1.48  fof(f35,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.48    inference(nnf_transformation,[],[f22])).
% 7.32/1.48  
% 7.32/1.48  fof(f36,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.48    inference(flattening,[],[f35])).
% 7.32/1.48  
% 7.32/1.48  fof(f37,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.48    inference(rectify,[],[f36])).
% 7.32/1.48  
% 7.32/1.48  fof(f38,plain,(
% 7.32/1.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 7.32/1.48    introduced(choice_axiom,[])).
% 7.32/1.48  
% 7.32/1.48  fof(f39,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 7.32/1.48  
% 7.32/1.48  fof(f59,plain,(
% 7.32/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f39])).
% 7.32/1.48  
% 7.32/1.48  fof(f12,conjecture,(
% 7.32/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f13,negated_conjecture,(
% 7.32/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.32/1.48    inference(negated_conjecture,[],[f12])).
% 7.32/1.48  
% 7.32/1.48  fof(f29,plain,(
% 7.32/1.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.32/1.48    inference(ennf_transformation,[],[f13])).
% 7.32/1.48  
% 7.32/1.48  fof(f30,plain,(
% 7.32/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.32/1.48    inference(flattening,[],[f29])).
% 7.32/1.48  
% 7.32/1.48  fof(f42,plain,(
% 7.32/1.48    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.32/1.48    introduced(choice_axiom,[])).
% 7.32/1.48  
% 7.32/1.48  fof(f41,plain,(
% 7.32/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.32/1.48    introduced(choice_axiom,[])).
% 7.32/1.48  
% 7.32/1.48  fof(f40,plain,(
% 7.32/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.32/1.48    introduced(choice_axiom,[])).
% 7.32/1.48  
% 7.32/1.48  fof(f43,plain,(
% 7.32/1.48    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.32/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f42,f41,f40])).
% 7.32/1.48  
% 7.32/1.48  fof(f75,plain,(
% 7.32/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f5,axiom,(
% 7.32/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f16,plain,(
% 7.32/1.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.32/1.48    inference(ennf_transformation,[],[f5])).
% 7.32/1.48  
% 7.32/1.48  fof(f50,plain,(
% 7.32/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.32/1.48    inference(cnf_transformation,[],[f16])).
% 7.32/1.48  
% 7.32/1.48  fof(f6,axiom,(
% 7.32/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f17,plain,(
% 7.32/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.32/1.48    inference(ennf_transformation,[],[f6])).
% 7.32/1.48  
% 7.32/1.48  fof(f18,plain,(
% 7.32/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.32/1.48    inference(flattening,[],[f17])).
% 7.32/1.48  
% 7.32/1.48  fof(f33,plain,(
% 7.32/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.32/1.48    inference(nnf_transformation,[],[f18])).
% 7.32/1.48  
% 7.32/1.48  fof(f51,plain,(
% 7.32/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.32/1.48    inference(cnf_transformation,[],[f33])).
% 7.32/1.48  
% 7.32/1.48  fof(f74,plain,(
% 7.32/1.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f55,plain,(
% 7.32/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.32/1.48    inference(cnf_transformation,[],[f33])).
% 7.32/1.48  
% 7.32/1.48  fof(f82,plain,(
% 7.32/1.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.32/1.48    inference(equality_resolution,[],[f55])).
% 7.32/1.48  
% 7.32/1.48  fof(f7,axiom,(
% 7.32/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f19,plain,(
% 7.32/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.32/1.48    inference(ennf_transformation,[],[f7])).
% 7.32/1.48  
% 7.32/1.48  fof(f20,plain,(
% 7.32/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.32/1.48    inference(flattening,[],[f19])).
% 7.32/1.48  
% 7.32/1.48  fof(f34,plain,(
% 7.32/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.32/1.48    inference(nnf_transformation,[],[f20])).
% 7.32/1.48  
% 7.32/1.48  fof(f58,plain,(
% 7.32/1.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f34])).
% 7.32/1.48  
% 7.32/1.48  fof(f85,plain,(
% 7.32/1.48    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.32/1.48    inference(equality_resolution,[],[f58])).
% 7.32/1.48  
% 7.32/1.48  fof(f77,plain,(
% 7.32/1.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f72,plain,(
% 7.32/1.48    m1_pre_topc(sK2,sK1)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f10,axiom,(
% 7.32/1.48    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f25,plain,(
% 7.32/1.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.32/1.48    inference(ennf_transformation,[],[f10])).
% 7.32/1.48  
% 7.32/1.48  fof(f26,plain,(
% 7.32/1.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.32/1.48    inference(flattening,[],[f25])).
% 7.32/1.48  
% 7.32/1.48  fof(f66,plain,(
% 7.32/1.48    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f26])).
% 7.32/1.48  
% 7.32/1.48  fof(f69,plain,(
% 7.32/1.48    v2_pre_topc(sK1)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f68,plain,(
% 7.32/1.48    ~v2_struct_0(sK1)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f70,plain,(
% 7.32/1.48    l1_pre_topc(sK1)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f64,plain,(
% 7.32/1.48    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f26])).
% 7.32/1.48  
% 7.32/1.48  fof(f65,plain,(
% 7.32/1.48    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f26])).
% 7.32/1.48  
% 7.32/1.48  fof(f61,plain,(
% 7.32/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f39])).
% 7.32/1.48  
% 7.32/1.48  fof(f3,axiom,(
% 7.32/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f15,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.32/1.48    inference(ennf_transformation,[],[f3])).
% 7.32/1.48  
% 7.32/1.48  fof(f48,plain,(
% 7.32/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f15])).
% 7.32/1.48  
% 7.32/1.48  fof(f4,axiom,(
% 7.32/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f49,plain,(
% 7.32/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.32/1.48    inference(cnf_transformation,[],[f4])).
% 7.32/1.48  
% 7.32/1.48  fof(f2,axiom,(
% 7.32/1.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f14,plain,(
% 7.32/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.32/1.48    inference(ennf_transformation,[],[f2])).
% 7.32/1.48  
% 7.32/1.48  fof(f47,plain,(
% 7.32/1.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f14])).
% 7.32/1.48  
% 7.32/1.48  fof(f9,axiom,(
% 7.32/1.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f23,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.32/1.48    inference(ennf_transformation,[],[f9])).
% 7.32/1.48  
% 7.32/1.48  fof(f24,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.32/1.48    inference(flattening,[],[f23])).
% 7.32/1.48  
% 7.32/1.48  fof(f63,plain,(
% 7.32/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f24])).
% 7.32/1.48  
% 7.32/1.48  fof(f71,plain,(
% 7.32/1.48    ~v2_struct_0(sK2)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f76,plain,(
% 7.32/1.48    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f73,plain,(
% 7.32/1.48    v1_funct_1(sK3)),
% 7.32/1.48    inference(cnf_transformation,[],[f43])).
% 7.32/1.48  
% 7.32/1.48  fof(f46,plain,(
% 7.32/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f32])).
% 7.32/1.48  
% 7.32/1.48  fof(f44,plain,(
% 7.32/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.32/1.48    inference(cnf_transformation,[],[f32])).
% 7.32/1.48  
% 7.32/1.48  fof(f79,plain,(
% 7.32/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.32/1.48    inference(equality_resolution,[],[f44])).
% 7.32/1.48  
% 7.32/1.48  fof(f60,plain,(
% 7.32/1.48    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f39])).
% 7.32/1.48  
% 7.32/1.48  fof(f62,plain,(
% 7.32/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f39])).
% 7.32/1.48  
% 7.32/1.48  fof(f11,axiom,(
% 7.32/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 7.32/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.48  
% 7.32/1.48  fof(f27,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.32/1.48    inference(ennf_transformation,[],[f11])).
% 7.32/1.48  
% 7.32/1.48  fof(f28,plain,(
% 7.32/1.48    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.32/1.48    inference(flattening,[],[f27])).
% 7.32/1.48  
% 7.32/1.48  fof(f67,plain,(
% 7.32/1.48    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.32/1.48    inference(cnf_transformation,[],[f28])).
% 7.32/1.48  
% 7.32/1.48  fof(f52,plain,(
% 7.32/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.32/1.48    inference(cnf_transformation,[],[f33])).
% 7.32/1.48  
% 7.32/1.48  fof(f84,plain,(
% 7.32/1.48    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.32/1.48    inference(equality_resolution,[],[f52])).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1,plain,
% 7.32/1.48      ( r1_tarski(X0,X0) ),
% 7.32/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1576,plain,
% 7.32/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_18,plain,
% 7.32/1.48      ( ~ r1_tarski(X0,X1)
% 7.32/1.48      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.32/1.48      | ~ v1_funct_1(X1)
% 7.32/1.48      | ~ v1_funct_1(X0)
% 7.32/1.48      | ~ v1_relat_1(X0)
% 7.32/1.48      | ~ v1_relat_1(X1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1568,plain,
% 7.32/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.32/1.48      | v1_funct_1(X1) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_26,negated_conjecture,
% 7.32/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.32/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1566,plain,
% 7.32/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_6,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.32/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.32/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1572,plain,
% 7.32/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.32/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2041,plain,
% 7.32/1.48      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_1566,c_1572]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_12,plain,
% 7.32/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.32/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.32/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.32/1.48      | k1_xboole_0 = X2 ),
% 7.32/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_27,negated_conjecture,
% 7.32/1.48      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.32/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_823,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.32/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.32/1.48      | u1_struct_0(sK1) != X2
% 7.32/1.48      | u1_struct_0(sK2) != X1
% 7.32/1.48      | sK3 != X0
% 7.32/1.48      | k1_xboole_0 = X2 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_824,plain,
% 7.32/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.48      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_823]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_826,plain,
% 7.32/1.48      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_824,c_26]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2048,plain,
% 7.32/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 7.32/1.48      inference(demodulation,[status(thm)],[c_2041,c_826]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_8,plain,
% 7.32/1.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.32/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.32/1.48      | k1_xboole_0 = X1
% 7.32/1.48      | k1_xboole_0 = X0 ),
% 7.32/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_761,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.32/1.48      | u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.48      | u1_struct_0(sK2) != X1
% 7.32/1.48      | sK3 != X0
% 7.32/1.48      | k1_xboole_0 = X0
% 7.32/1.48      | k1_xboole_0 = X1 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_762,plain,
% 7.32/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.48      | u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK2)
% 7.32/1.48      | k1_xboole_0 = sK3 ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_761]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1560,plain,
% 7.32/1.48      ( u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK2)
% 7.32/1.48      | k1_xboole_0 = sK3
% 7.32/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2278,plain,
% 7.32/1.48      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.48      | sK3 = k1_xboole_0
% 7.32/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_2048,c_1560]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_13,plain,
% 7.32/1.48      ( r2_funct_2(X0,X1,X2,X2)
% 7.32/1.48      | ~ v1_funct_2(X2,X0,X1)
% 7.32/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.32/1.48      | ~ v1_funct_1(X2) ),
% 7.32/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_24,negated_conjecture,
% 7.32/1.48      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_370,plain,
% 7.32/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.32/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.32/1.48      | ~ v1_funct_1(X0)
% 7.32/1.48      | k4_tmap_1(sK1,sK2) != X0
% 7.32/1.48      | u1_struct_0(sK1) != X2
% 7.32/1.48      | u1_struct_0(sK2) != X1
% 7.32/1.48      | sK3 != X0 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_371,plain,
% 7.32/1.48      ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.48      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.48      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.48      | sK3 != k4_tmap_1(sK1,sK2) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_370]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_29,negated_conjecture,
% 7.32/1.48      ( m1_pre_topc(sK2,sK1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_20,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.48      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.32/1.48      | ~ v2_pre_topc(X1)
% 7.32/1.48      | ~ l1_pre_topc(X1)
% 7.32/1.48      | v2_struct_0(X1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_32,negated_conjecture,
% 7.32/1.48      ( v2_pre_topc(sK1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_454,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.48      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.32/1.48      | ~ l1_pre_topc(X1)
% 7.32/1.48      | v2_struct_0(X1)
% 7.32/1.48      | sK1 != X1 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_455,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.48      | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.32/1.48      | ~ l1_pre_topc(sK1)
% 7.32/1.48      | v2_struct_0(sK1) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_454]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_33,negated_conjecture,
% 7.32/1.48      ( ~ v2_struct_0(sK1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_31,negated_conjecture,
% 7.32/1.48      ( l1_pre_topc(sK1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_459,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.48      | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_455,c_33,c_31]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_534,plain,
% 7.32/1.48      ( m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.32/1.48      | sK1 != sK1
% 7.32/1.48      | sK2 != X0 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_29,c_459]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_535,plain,
% 7.32/1.48      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_534]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_22,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.48      | ~ v2_pre_topc(X1)
% 7.32/1.48      | ~ l1_pre_topc(X1)
% 7.32/1.48      | v2_struct_0(X1)
% 7.32/1.48      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 7.32/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_436,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.48      | ~ l1_pre_topc(X1)
% 7.32/1.48      | v2_struct_0(X1)
% 7.32/1.48      | v1_funct_1(k4_tmap_1(X1,X0))
% 7.32/1.48      | sK1 != X1 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_437,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.48      | ~ l1_pre_topc(sK1)
% 7.32/1.48      | v2_struct_0(sK1)
% 7.32/1.48      | v1_funct_1(k4_tmap_1(sK1,X0)) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_436]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_441,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,sK1) | v1_funct_1(k4_tmap_1(sK1,X0)) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_437,c_33,c_31]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_541,plain,
% 7.32/1.48      ( v1_funct_1(k4_tmap_1(sK1,X0)) | sK1 != sK1 | sK2 != X0 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_29,c_441]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_542,plain,
% 7.32/1.48      ( v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_541]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_21,plain,
% 7.32/1.48      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.32/1.48      | ~ m1_pre_topc(X1,X0)
% 7.32/1.48      | ~ v2_pre_topc(X0)
% 7.32/1.48      | ~ l1_pre_topc(X0)
% 7.32/1.48      | v2_struct_0(X0) ),
% 7.32/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_391,plain,
% 7.32/1.48      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.32/1.48      | ~ m1_pre_topc(X1,X0)
% 7.32/1.48      | ~ l1_pre_topc(X0)
% 7.32/1.48      | v2_struct_0(X0)
% 7.32/1.48      | sK1 != X0 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_392,plain,
% 7.32/1.48      ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
% 7.32/1.48      | ~ m1_pre_topc(X0,sK1)
% 7.32/1.48      | ~ l1_pre_topc(sK1)
% 7.32/1.48      | v2_struct_0(sK1) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_391]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_396,plain,
% 7.32/1.48      ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
% 7.32/1.48      | ~ m1_pre_topc(X0,sK1) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_392,c_33,c_31]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_569,plain,
% 7.32/1.48      ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
% 7.32/1.48      | sK1 != sK1
% 7.32/1.48      | sK2 != X0 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_29,c_396]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_570,plain,
% 7.32/1.48      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_569]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1167,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1799,plain,
% 7.32/1.48      ( k4_tmap_1(sK1,sK2) != X0 | sK3 != X0 | sK3 = k4_tmap_1(sK1,sK2) ),
% 7.32/1.48      inference(instantiation,[status(thm)],[c_1167]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1800,plain,
% 7.32/1.48      ( k4_tmap_1(sK1,sK2) != k1_xboole_0
% 7.32/1.48      | sK3 = k4_tmap_1(sK1,sK2)
% 7.32/1.48      | sK3 != k1_xboole_0 ),
% 7.32/1.48      inference(instantiation,[status(thm)],[c_1799]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1563,plain,
% 7.32/1.48      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2202,plain,
% 7.32/1.48      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_2048,c_1563]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2216,plain,
% 7.32/1.48      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.48      | u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 7.32/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_2202]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2203,plain,
% 7.32/1.48      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_2048,c_1566]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2217,plain,
% 7.32/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.48      | u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 7.32/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_2203]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2279,plain,
% 7.32/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.48      | u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.48      | sK3 = k1_xboole_0 ),
% 7.32/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_2278]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_777,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.32/1.48      | k4_tmap_1(sK1,sK2) != X0
% 7.32/1.48      | u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.48      | u1_struct_0(sK2) != X1
% 7.32/1.48      | k1_xboole_0 = X0
% 7.32/1.48      | k1_xboole_0 = X1 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_570]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_778,plain,
% 7.32/1.48      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.48      | u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.48      | k1_xboole_0 = k4_tmap_1(sK1,sK2)
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK2) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_777]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1559,plain,
% 7.32/1.48      ( u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.48      | k1_xboole_0 = k4_tmap_1(sK1,sK2)
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK2)
% 7.32/1.48      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2401,plain,
% 7.32/1.48      ( k4_tmap_1(sK1,sK2) = k1_xboole_0
% 7.32/1.48      | u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.48      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_2048,c_1559]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2402,plain,
% 7.32/1.48      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.48      | k4_tmap_1(sK1,sK2) = k1_xboole_0
% 7.32/1.48      | u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_2401]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2966,plain,
% 7.32/1.48      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.32/1.48      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_2278,c_371,c_535,c_542,c_570,c_1800,c_2216,c_2217,
% 7.32/1.48                 c_2279,c_2402]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2042,plain,
% 7.32/1.48      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_1563,c_1572]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_834,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.32/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.32/1.48      | k4_tmap_1(sK1,sK2) != X0
% 7.32/1.48      | u1_struct_0(sK1) != X2
% 7.32/1.48      | u1_struct_0(sK2) != X1
% 7.32/1.48      | k1_xboole_0 = X2 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_12,c_570]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_835,plain,
% 7.32/1.48      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.48      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_834]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_837,plain,
% 7.32/1.48      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
% 7.32/1.48      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_835,c_535]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2283,plain,
% 7.32/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | k1_relat_1(k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2) ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_2042,c_837]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_16,plain,
% 7.32/1.48      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 7.32/1.48      | r1_tarski(X0,X1)
% 7.32/1.48      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.32/1.48      | ~ v1_funct_1(X1)
% 7.32/1.48      | ~ v1_funct_1(X0)
% 7.32/1.48      | ~ v1_relat_1(X0)
% 7.32/1.48      | ~ v1_relat_1(X1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1570,plain,
% 7.32/1.48      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.32/1.48      | r1_tarski(X0,X1) = iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 7.32/1.48      | v1_funct_1(X1) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_3065,plain,
% 7.32/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.48      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top
% 7.32/1.48      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.48      | v1_relat_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_2283,c_1570]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_536,plain,
% 7.32/1.48      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_543,plain,
% 7.32/1.48      ( v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_4,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.32/1.48      | ~ v1_relat_1(X1)
% 7.32/1.48      | v1_relat_1(X0) ),
% 7.32/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1769,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.32/1.48      | v1_relat_1(X0)
% 7.32/1.48      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.32/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1977,plain,
% 7.32/1.48      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.48      | v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.48      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.48      inference(instantiation,[status(thm)],[c_1769]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1978,plain,
% 7.32/1.48      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.32/1.48      | v1_relat_1(k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.48      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_1977]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_5,plain,
% 7.32/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.32/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2171,plain,
% 7.32/1.48      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_2172,plain,
% 7.32/1.48      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_4662,plain,
% 7.32/1.48      ( v1_relat_1(X0) != iProver_top
% 7.32/1.48      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.48      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_3065,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_4663,plain,
% 7.32/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.48      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.48      inference(renaming,[status(thm)],[c_4662]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_3,plain,
% 7.32/1.48      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.32/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1575,plain,
% 7.32/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.48      | m1_subset_1(X0,X1) = iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_4675,plain,
% 7.32/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.48      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top
% 7.32/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.48      inference(superposition,[status(thm)],[c_4663,c_1575]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_19,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.48      | m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.48      | ~ l1_pre_topc(X1)
% 7.32/1.48      | v2_struct_0(X1)
% 7.32/1.48      | v2_struct_0(X0) ),
% 7.32/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_487,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.48      | m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.48      | v2_struct_0(X0)
% 7.32/1.48      | v2_struct_0(X1)
% 7.32/1.48      | sK1 != X1 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_488,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.48      | m1_subset_1(X1,u1_struct_0(sK1))
% 7.32/1.48      | v2_struct_0(X0)
% 7.32/1.48      | v2_struct_0(sK1) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_487]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_492,plain,
% 7.32/1.48      ( v2_struct_0(X0)
% 7.32/1.48      | m1_subset_1(X1,u1_struct_0(sK1))
% 7.32/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.48      | ~ m1_pre_topc(X0,sK1) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_488,c_33]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_493,plain,
% 7.32/1.48      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.48      | m1_subset_1(X1,u1_struct_0(sK1))
% 7.32/1.48      | v2_struct_0(X0) ),
% 7.32/1.48      inference(renaming,[status(thm)],[c_492]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_516,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.48      | m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.48      | v2_struct_0(X1)
% 7.32/1.48      | sK1 != sK1
% 7.32/1.48      | sK2 != X1 ),
% 7.32/1.48      inference(resolution_lifted,[status(thm)],[c_29,c_493]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_517,plain,
% 7.32/1.48      ( m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.32/1.48      | v2_struct_0(sK2) ),
% 7.32/1.48      inference(unflattening,[status(thm)],[c_516]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_30,negated_conjecture,
% 7.32/1.48      ( ~ v2_struct_0(sK2) ),
% 7.32/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_521,plain,
% 7.32/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.32/1.48      | m1_subset_1(X0,u1_struct_0(sK1)) ),
% 7.32/1.48      inference(global_propositional_subsumption,
% 7.32/1.48                [status(thm)],
% 7.32/1.48                [c_517,c_30]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_522,plain,
% 7.32/1.48      ( m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 7.32/1.48      inference(renaming,[status(thm)],[c_521]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_1564,plain,
% 7.32/1.48      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 7.32/1.48      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.32/1.48      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 7.32/1.48  
% 7.32/1.48  cnf(c_5047,plain,
% 7.32/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.48      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) = iProver_top
% 7.32/1.48      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.48      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.48      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4675,c_1564]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_25,negated_conjecture,
% 7.32/1.49      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.32/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.49      | k1_funct_1(sK3,X0) = X0 ),
% 7.32/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1567,plain,
% 7.32/1.49      ( k1_funct_1(sK3,X0) = X0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4677,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4663,c_1567]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5300,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_5047,c_4677]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5436,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2283,c_5300]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5600,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_5436]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5780,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1568,c_5600]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_28,negated_conjecture,
% 7.32/1.49      ( v1_funct_1(sK3) ),
% 7.32/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_39,plain,
% 7.32/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_41,plain,
% 7.32/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1974,plain,
% 7.32/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | v1_relat_1(sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1769]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1975,plain,
% 7.32/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.32/1.49      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_6294,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_5780,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_6295,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_6294]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_0,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.32/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1577,plain,
% 7.32/1.49      ( X0 = X1
% 7.32/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.32/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2537,plain,
% 7.32/1.49      ( k1_relat_1(X0) = k1_relat_1(X1)
% 7.32/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X1) != iProver_top
% 7.32/1.49      | v1_relat_1(X1) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1568,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3470,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2283,c_2537]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4647,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3470,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4648,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_4647]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_6312,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_6295,c_4648]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13776,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_6312]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14309,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(X0,sK3) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1568,c_13776]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2,plain,
% 7.32/1.49      ( r1_tarski(X0,X0) ),
% 7.32/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_106,plain,
% 7.32/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_110,plain,
% 7.32/1.49      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.32/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1175,plain,
% 7.32/1.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.32/1.49      theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1774,plain,
% 7.32/1.49      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1175]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1775,plain,
% 7.32/1.49      ( X0 != sK3
% 7.32/1.49      | v1_funct_1(X0) = iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1837,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1838,plain,
% 7.32/1.49      ( X0 = sK3
% 7.32/1.49      | r1_tarski(X0,sK3) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_1837]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1166,plain,( X0 = X0 ),theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1852,plain,
% 7.32/1.49      ( sK3 = sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1802,plain,
% 7.32/1.49      ( u1_struct_0(sK2) != X0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_xboole_0 != X0 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1167]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1908,plain,
% 7.32/1.49      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_xboole_0 != u1_struct_0(sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1802]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1909,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1966,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = k4_tmap_1(sK1,sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2010,plain,
% 7.32/1.49      ( u1_struct_0(sK1) != X0
% 7.32/1.49      | k1_xboole_0 != X0
% 7.32/1.49      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1167]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2011,plain,
% 7.32/1.49      ( u1_struct_0(sK1) != k1_xboole_0
% 7.32/1.49      | k1_xboole_0 = u1_struct_0(sK1)
% 7.32/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2010]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1997,plain,
% 7.32/1.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1167]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2262,plain,
% 7.32/1.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1997]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2263,plain,
% 7.32/1.49      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2262]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1171,plain,
% 7.32/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.32/1.49      theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2405,plain,
% 7.32/1.49      ( v1_relat_1(X0) | ~ v1_relat_1(sK3) | X0 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1171]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2406,plain,
% 7.32/1.49      ( X0 != sK3
% 7.32/1.49      | v1_relat_1(X0) = iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_2405]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2130,plain,
% 7.32/1.49      ( X0 != X1 | k4_tmap_1(sK1,sK2) != X1 | k4_tmap_1(sK1,sK2) = X0 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1167]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2807,plain,
% 7.32/1.49      ( X0 != k4_tmap_1(sK1,sK2)
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = X0
% 7.32/1.49      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2130]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2808,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = k1_xboole_0
% 7.32/1.49      | k1_xboole_0 != k4_tmap_1(sK1,sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2807]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1173,plain,
% 7.32/1.49      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.32/1.49      theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2190,plain,
% 7.32/1.49      ( X0 != u1_struct_0(sK1)
% 7.32/1.49      | X1 != u1_struct_0(sK2)
% 7.32/1.49      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1173]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2839,plain,
% 7.32/1.49      ( X0 != u1_struct_0(sK1)
% 7.32/1.49      | k2_zfmisc_1(u1_struct_0(sK2),X0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.49      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2190]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2840,plain,
% 7.32/1.49      ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.49      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.32/1.49      | k1_xboole_0 != u1_struct_0(sK1) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2839]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1172,plain,
% 7.32/1.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.32/1.49      theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1938,plain,
% 7.32/1.49      ( X0 != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.49      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2189,plain,
% 7.32/1.49      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1938]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5147,plain,
% 7.32/1.49      ( k2_zfmisc_1(u1_struct_0(sK2),X0) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2189]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5148,plain,
% 7.32/1.49      ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_5147]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1169,plain,
% 7.32/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.32/1.49      theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1829,plain,
% 7.32/1.49      ( m1_subset_1(X0,X1)
% 7.32/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | X0 != k4_tmap_1(sK1,sK2)
% 7.32/1.49      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1169]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1965,plain,
% 7.32/1.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1829]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14575,plain,
% 7.32/1.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
% 7.32/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1965]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14578,plain,
% 7.32/1.49      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.49      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_14575]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1824,plain,
% 7.32/1.49      ( m1_subset_1(X0,X1)
% 7.32/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | X0 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1169]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1851,plain,
% 7.32/1.49      ( m1_subset_1(sK3,X0)
% 7.32/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | sK3 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1824]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1937,plain,
% 7.32/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
% 7.32/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | sK3 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1851]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14588,plain,
% 7.32/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
% 7.32/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | sK3 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1937]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14590,plain,
% 7.32/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.32/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.32/1.49      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.32/1.49      | sK3 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_14588]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14800,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(X0)
% 7.32/1.49      | r1_tarski(X0,sK3) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_14309,c_39,c_26,c_41,c_106,c_110,c_371,c_535,c_542,
% 7.32/1.49                 c_570,c_762,c_778,c_1775,c_1800,c_1838,c_1852,c_1908,
% 7.32/1.49                 c_1909,c_1966,c_1975,c_2011,c_2172,c_2263,c_2406,c_2808,
% 7.32/1.49                 c_2840,c_5148,c_14578,c_14590]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14811,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
% 7.32/1.49      | r1_tarski(sK3,sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1576,c_14800]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2734,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2283,c_1568]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4048,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_2734,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4049,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_4048]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4059,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1576,c_4049]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4302,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_4059,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4309,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_4302]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2733,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2283,c_1568]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3677,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_2733,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3678,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_3677]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3688,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1576,c_3678]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3779,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3688,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3785,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_3779]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3852,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3785,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4474,plain,
% 7.32/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4309,c_3852]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14914,plain,
% 7.32/1.49      ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_14811,c_26,c_106,c_110,c_371,c_535,c_542,c_570,c_762,
% 7.32/1.49                 c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_2011,c_2263,
% 7.32/1.49                 c_2808,c_2840,c_4474,c_5148,c_14578,c_14590]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14915,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3) ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_14914]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14958,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK3)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_14915,c_1568]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1790,plain,
% 7.32/1.49      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | sK3 = k4_tmap_1(sK1,sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2500,plain,
% 7.32/1.49      ( r1_tarski(sK3,sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1809,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,sK3)
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
% 7.32/1.49      | ~ v1_funct_1(X0)
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(X0)
% 7.32/1.49      | ~ v1_relat_1(sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3220,plain,
% 7.32/1.49      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 7.32/1.49      | ~ r1_tarski(sK3,sK3)
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1809]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4193,plain,
% 7.32/1.49      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1168,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.32/1.49      theory(equality) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3215,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,X1)
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) != X0
% 7.32/1.49      | k1_relat_1(sK3) != X1 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1168]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_6446,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) != X0
% 7.32/1.49      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_3215]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13500,plain,
% 7.32/1.49      ( r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.32/1.49      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 7.32/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) != k1_relat_1(sK3)
% 7.32/1.49      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_6446]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14949,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_14915,c_1568]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15311,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_14949,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15312,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_15311]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15322,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1576,c_15312]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15335,plain,
% 7.32/1.49      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_15322]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5435,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4309,c_5300]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5478,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_5435,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17,plain,
% 7.32/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.32/1.49      | ~ r1_tarski(X1,X2)
% 7.32/1.49      | ~ v1_funct_1(X2)
% 7.32/1.49      | ~ v1_funct_1(X1)
% 7.32/1.49      | ~ v1_relat_1(X1)
% 7.32/1.49      | ~ v1_relat_1(X2)
% 7.32/1.49      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 7.32/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1569,plain,
% 7.32/1.49      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 7.32/1.49      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 7.32/1.49      | r1_tarski(X2,X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X2) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X2) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2732,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.32/1.49      | v1_funct_1(X1) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X1) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2283,c_1569]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4232,plain,
% 7.32/1.49      ( v1_relat_1(X1) != iProver_top
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.32/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_2732,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4233,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.32/1.49      | v1_funct_1(X1) != iProver_top
% 7.32/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_4232]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5490,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_5478,c_4233]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12636,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_5490,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12648,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_12636]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12687,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1570,c_12648]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13340,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_12687,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13341,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_13340]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13356,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3785,c_13341]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2023,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) != sK3
% 7.32/1.49      | sK3 = k4_tmap_1(sK1,sK2)
% 7.32/1.49      | sK3 != sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1799]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15,plain,
% 7.32/1.49      ( r1_tarski(X0,X1)
% 7.32/1.49      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.32/1.49      | ~ v1_funct_1(X1)
% 7.32/1.49      | ~ v1_funct_1(X0)
% 7.32/1.49      | ~ v1_relat_1(X0)
% 7.32/1.49      | ~ v1_relat_1(X1)
% 7.32/1.49      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 7.32/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2058,plain,
% 7.32/1.49      ( r1_tarski(X0,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | ~ v1_funct_1(X0)
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(X0)
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0,k4_tmap_1(sK1,sK2))) != k1_funct_1(X0,sK0(X0,k4_tmap_1(sK1,sK2))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3138,plain,
% 7.32/1.49      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_2058]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5487,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_5478,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5515,plain,
% 7.32/1.49      ( ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5487]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13412,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_13356]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15768,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_13356,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,
% 7.32/1.49                 c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,
% 7.32/1.49                 c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,
% 7.32/1.49                 c_5148,c_5515,c_13412,c_14578,c_14590,c_15335]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15770,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_15768]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15772,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15768,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,
% 7.32/1.49                 c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,
% 7.32/1.49                 c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,
% 7.32/1.49                 c_5148,c_5515,c_13412,c_14578,c_14590,c_15335]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15773,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_15772]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23,plain,
% 7.32/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.32/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.49      | ~ v2_pre_topc(X1)
% 7.32/1.49      | ~ l1_pre_topc(X1)
% 7.32/1.49      | v2_struct_0(X1)
% 7.32/1.49      | v2_struct_0(X0)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 7.32/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_409,plain,
% 7.32/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.32/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.32/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.49      | ~ l1_pre_topc(X1)
% 7.32/1.49      | v2_struct_0(X0)
% 7.32/1.49      | v2_struct_0(X1)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
% 7.32/1.49      | sK1 != X1 ),
% 7.32/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_410,plain,
% 7.32/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.49      | ~ r2_hidden(X1,u1_struct_0(X0))
% 7.32/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.32/1.49      | ~ l1_pre_topc(sK1)
% 7.32/1.49      | v2_struct_0(X0)
% 7.32/1.49      | v2_struct_0(sK1)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
% 7.32/1.49      inference(unflattening,[status(thm)],[c_409]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_414,plain,
% 7.32/1.49      ( v2_struct_0(X0)
% 7.32/1.49      | ~ m1_pre_topc(X0,sK1)
% 7.32/1.49      | ~ r2_hidden(X1,u1_struct_0(X0))
% 7.32/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_410,c_33,c_31]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_415,plain,
% 7.32/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.32/1.49      | ~ r2_hidden(X1,u1_struct_0(X0))
% 7.32/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.32/1.49      | v2_struct_0(X0)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_414]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_548,plain,
% 7.32/1.49      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 7.32/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.49      | v2_struct_0(X1)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,X1),X0) = X0
% 7.32/1.49      | sK1 != sK1
% 7.32/1.49      | sK2 != X1 ),
% 7.32/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_415]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_549,plain,
% 7.32/1.49      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.32/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.49      | v2_struct_0(sK2)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.32/1.49      inference(unflattening,[status(thm)],[c_548]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_553,plain,
% 7.32/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.49      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_549,c_30]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_554,plain,
% 7.32/1.49      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.32/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_553]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1561,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4676,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4663,c_1561]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5299,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_5047,c_4676]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5639,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4309,c_5299]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11523,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_5639,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11543,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_11523,c_4233]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12781,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_11543,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12793,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_12781]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12832,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1570,c_12793]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14108,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_12832,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14109,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_14108]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14124,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3785,c_14109]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11535,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_11523,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11688,plain,
% 7.32/1.49      ( ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_11535]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14180,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_14124]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15900,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_14124,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,
% 7.32/1.49                 c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,
% 7.32/1.49                 c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,
% 7.32/1.49                 c_5148,c_11688,c_14180,c_14578,c_14590,c_15335]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15902,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_15900]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15904,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15900,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,
% 7.32/1.49                 c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,
% 7.32/1.49                 c_1977,c_2011,c_2023,c_2171,c_2263,c_2808,c_2840,c_3138,
% 7.32/1.49                 c_5148,c_11688,c_14180,c_14578,c_14590,c_15335]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15905,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_15904]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1571,plain,
% 7.32/1.49      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 7.32/1.49      | r1_tarski(X1,X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(X1) != iProver_top
% 7.32/1.49      | v1_relat_1(X1) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15908,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_15905,c_1571]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15909,plain,
% 7.32/1.49      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_15908]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15443,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15322,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3066,plain,
% 7.32/1.49      ( m1_subset_1(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.32/1.49      | r1_tarski(X0,X1) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 7.32/1.49      | v1_funct_1(X1) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1570,c_1575]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2980,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 7.32/1.49      | m1_subset_1(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_1564]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3637,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3066,c_2980]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4115,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3637,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4116,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_4115]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2982,plain,
% 7.32/1.49      ( k1_funct_1(sK3,X0) = X0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_1567]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3234,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1570,c_2982]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3421,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3234,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3422,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_3421]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4128,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4116,c_3422]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15466,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_15443,c_4128]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2505,plain,
% 7.32/1.49      ( r1_tarski(sK3,sK3) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_2500]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3221,plain,
% 7.32/1.49      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,sK3) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_3220]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14945,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_14915,c_4128]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15564,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15466,c_39,c_41,c_536,c_543,c_1975,c_1978,c_2172,
% 7.32/1.49                 c_2505,c_3221,c_14945]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15575,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_15564,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4153,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3785,c_4128]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11700,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_4153,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11712,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_11700,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11886,plain,
% 7.32/1.49      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_11712]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16157,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15575,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,
% 7.32/1.49                 c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,
% 7.32/1.49                 c_1977,c_2011,c_2023,c_2171,c_2263,c_2500,c_2808,c_2840,
% 7.32/1.49                 c_3138,c_3220,c_4193,c_4474,c_5148,c_5515,c_11886,
% 7.32/1.49                 c_13412,c_13500,c_14578,c_14590,c_15335,c_15909]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16158,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_16157]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2977,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2966,c_1561]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3318,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK1)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1570,c_2977]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5988,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3318,c_39,c_41,c_1975,c_2172,c_3637]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5989,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_5988]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15464,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_15443,c_5989]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14938,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_14915,c_5989]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15700,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15464,c_39,c_41,c_536,c_543,c_1975,c_1978,c_2172,
% 7.32/1.49                 c_2505,c_3221,c_14938]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_15711,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_15700,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_6002,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3785,c_5989]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12060,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_6002,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12072,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_12060,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_12255,plain,
% 7.32/1.49      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK1) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_12072]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16299,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_15711,c_28,c_26,c_106,c_110,c_371,c_535,c_542,c_570,
% 7.32/1.49                 c_762,c_778,c_1800,c_1852,c_1908,c_1909,c_1966,c_1974,
% 7.32/1.49                 c_1977,c_2011,c_2023,c_2171,c_2263,c_2500,c_2808,c_2840,
% 7.32/1.49                 c_3138,c_3220,c_4193,c_4474,c_5148,c_5515,c_12255,
% 7.32/1.49                 c_13412,c_13500,c_14578,c_14590,c_15335,c_15909]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16300,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_16299]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16303,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16300,c_1571]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16304,plain,
% 7.32/1.49      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_16303]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16306,plain,
% 7.32/1.49      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_14958,c_28,c_26,c_371,c_535,c_542,c_570,c_1790,c_1974,
% 7.32/1.49                 c_1977,c_2171,c_2500,c_3220,c_4193,c_13500,c_14915,
% 7.32/1.49                 c_15335,c_15773,c_15909,c_16158,c_16304]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11,plain,
% 7.32/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.32/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.32/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.32/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_810,plain,
% 7.32/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.32/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.32/1.49      | k4_tmap_1(sK1,sK2) != X0
% 7.32/1.49      | u1_struct_0(sK1) != X1
% 7.32/1.49      | u1_struct_0(sK2) != k1_xboole_0 ),
% 7.32/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_570]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_811,plain,
% 7.32/1.49      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 7.32/1.49      | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) != k1_xboole_0 ),
% 7.32/1.49      inference(unflattening,[status(thm)],[c_810]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1557,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) != k1_xboole_0
% 7.32/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16418,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.32/1.49      | k1_xboole_0 != k1_xboole_0
% 7.32/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1557]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16468,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(equality_resolution_simp,[status(thm)],[c_16418]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16419,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_2042]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16469,plain,
% 7.32/1.49      ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16468,c_16419]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16428,plain,
% 7.32/1.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1563]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16472,plain,
% 7.32/1.49      ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 7.32/1.49      inference(forward_subsumption_resolution,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_16469,c_16428]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_797,plain,
% 7.32/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.32/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK1) != X1
% 7.32/1.49      | u1_struct_0(sK2) != k1_xboole_0
% 7.32/1.49      | sK3 != X0 ),
% 7.32/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_798,plain,
% 7.32/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 7.32/1.49      | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) != k1_xboole_0 ),
% 7.32/1.49      inference(unflattening,[status(thm)],[c_797]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1558,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.32/1.49      | u1_struct_0(sK2) != k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16423,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.32/1.49      | k1_xboole_0 != k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1558]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16457,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(equality_resolution_simp,[status(thm)],[c_16423]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16425,plain,
% 7.32/1.49      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_2041]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16458,plain,
% 7.32/1.49      ( k1_relat_1(sK3) = k1_xboole_0
% 7.32/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16457,c_16425]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16430,plain,
% 7.32/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1566]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16461,plain,
% 7.32/1.49      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.32/1.49      inference(forward_subsumption_resolution,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_16458,c_16430]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17062,plain,
% 7.32/1.49      ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16461,c_1570]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17197,plain,
% 7.32/1.49      ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_17062,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_19069,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_17197,c_39,c_41,c_1975,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_19070,plain,
% 7.32/1.49      ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_19069]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16427,plain,
% 7.32/1.49      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 7.32/1.49      | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1564]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16424,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.32/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1561]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17712,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.32/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16427,c_16424]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_18517,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.32/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.32/1.49      inference(forward_subsumption_resolution,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_17712,c_1575]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_19081,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_19070,c_18517]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20943,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16472,c_19081]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_105,plain,
% 7.32/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_107,plain,
% 7.32/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_105]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22319,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_20943,c_107,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22320,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_22319]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17787,plain,
% 7.32/1.49      ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16472,c_1570]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17922,plain,
% 7.32/1.49      ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_17787,c_16472]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20961,plain,
% 7.32/1.49      ( v1_relat_1(X0) != iProver_top
% 7.32/1.49      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_17922,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20962,plain,
% 7.32/1.49      ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_20961]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20973,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_20962,c_18517]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_21664,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = X0
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_20973,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22330,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22320,c_21664]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22398,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22330,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16429,plain,
% 7.32/1.49      ( k1_funct_1(sK3,X0) = X0
% 7.32/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16306,c_1567]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17459,plain,
% 7.32/1.49      ( k1_funct_1(sK3,X0) = X0
% 7.32/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.32/1.49      | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16427,c_16429]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17489,plain,
% 7.32/1.49      ( k1_funct_1(sK3,X0) = X0
% 7.32/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.32/1.49      inference(forward_subsumption_resolution,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_17459,c_1575]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20974,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_20962,c_17489]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_21147,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = X0
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.32/1.49      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_20974,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22331,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22320,c_21147]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22385,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22331,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22441,plain,
% 7.32/1.49      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(sK3)
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_22385]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22444,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22385,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,
% 7.32/1.49                 c_1975,c_2023,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22445,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_22444]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22327,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22320,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22538,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22327,c_371,c_535,c_542,c_570,c_1852,c_2023]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22546,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_20973,c_22538]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22553,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22546,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22561,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22553,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,
% 7.32/1.49                 c_1975,c_2023,c_2172,c_22398]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22562,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_22561]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22565,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22562,c_1571]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22566,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22565,c_16461,c_16472]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22918,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22398,c_39,c_41,c_107,c_536,c_543,c_1975,c_1978,
% 7.32/1.49                 c_2172,c_22445,c_22538,c_22566]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22921,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22918,c_1571]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_19082,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.32/1.49      | r1_tarski(sK3,X0) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.32/1.49      | v1_funct_1(X0) != iProver_top
% 7.32/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_19070,c_17489]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20836,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16472,c_19082]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22078,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_20836,c_107,c_536,c_543,c_1978,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22079,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_22078]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22089,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22079,c_21664]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22157,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22089,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22258,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22157,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,
% 7.32/1.49                 c_1975,c_2023,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22259,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(renaming,[status(thm)],[c_22258]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22262,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22259,c_1571]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22263,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22262,c_16461,c_16472]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22086,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22079,c_1577]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22196,plain,
% 7.32/1.49      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_22086]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22090,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22079,c_21147]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22144,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22090,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22264,plain,
% 7.32/1.49      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.32/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_funct_1(sK3)
% 7.32/1.49      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.32/1.49      | ~ v1_relat_1(sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_22263]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22266,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22263,c_28,c_39,c_26,c_41,c_106,c_107,c_371,c_535,
% 7.32/1.49                 c_542,c_570,c_1852,c_1974,c_1975,c_1977,c_2023,c_2171,
% 7.32/1.49                 c_2172,c_22196,c_22144,c_22264]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22922,plain,
% 7.32/1.49      ( sK0(sK3,k4_tmap_1(sK1,sK2)) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22921,c_16461,c_16472,c_22266]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22923,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(equality_resolution_simp,[status(thm)],[c_22922]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22926,plain,
% 7.32/1.49      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22923,c_39,c_41,c_107,c_536,c_543,c_1975,c_1978,
% 7.32/1.49                 c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22936,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22926,c_21664]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22995,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22936,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23198,plain,
% 7.32/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22995,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,
% 7.32/1.49                 c_1975,c_2023,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23201,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_23198,c_1571]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22937,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_22926,c_21147]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22984,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_22937,c_16461]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23194,plain,
% 7.32/1.49      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.32/1.49      inference(global_propositional_subsumption,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_22984,c_39,c_41,c_107,c_371,c_535,c_542,c_570,c_1852,
% 7.32/1.49                 c_1975,c_2023,c_2172]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23202,plain,
% 7.32/1.49      ( sK0(k4_tmap_1(sK1,sK2),sK3) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_23201,c_16461,c_16472,c_23194]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23203,plain,
% 7.32/1.49      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.32/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.32/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_funct_1(sK3) != iProver_top
% 7.32/1.49      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.32/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.32/1.49      inference(equality_resolution_simp,[status(thm)],[c_23202]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_18491,plain,
% 7.32/1.49      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.32/1.49      | ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.32/1.49      | k4_tmap_1(sK1,sK2) = sK3 ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_1837]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_18492,plain,
% 7.32/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.32/1.49      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top
% 7.32/1.49      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_18491]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(contradiction,plain,
% 7.32/1.49      ( $false ),
% 7.32/1.49      inference(minisat,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_23203,c_22923,c_18492,c_2172,c_2023,c_1978,c_1975,
% 7.32/1.49                 c_1852,c_570,c_543,c_542,c_536,c_535,c_371,c_107,c_41,
% 7.32/1.49                 c_39]) ).
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  ------                               Statistics
% 7.32/1.49  
% 7.32/1.49  ------ General
% 7.32/1.49  
% 7.32/1.49  abstr_ref_over_cycles:                  0
% 7.32/1.49  abstr_ref_under_cycles:                 0
% 7.32/1.49  gc_basic_clause_elim:                   0
% 7.32/1.49  forced_gc_time:                         0
% 7.32/1.49  parsing_time:                           0.012
% 7.32/1.49  unif_index_cands_time:                  0.
% 7.32/1.49  unif_index_add_time:                    0.
% 7.32/1.49  orderings_time:                         0.
% 7.32/1.49  out_proof_time:                         0.033
% 7.32/1.49  total_time:                             0.597
% 7.32/1.49  num_of_symbols:                         54
% 7.32/1.49  num_of_terms:                           6683
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing
% 7.32/1.49  
% 7.32/1.49  num_of_splits:                          0
% 7.32/1.49  num_of_split_atoms:                     0
% 7.32/1.49  num_of_reused_defs:                     0
% 7.32/1.49  num_eq_ax_congr_red:                    11
% 7.32/1.49  num_of_sem_filtered_clauses:            1
% 7.32/1.49  num_of_subtypes:                        0
% 7.32/1.49  monotx_restored_types:                  0
% 7.32/1.49  sat_num_of_epr_types:                   0
% 7.32/1.49  sat_num_of_non_cyclic_types:            0
% 7.32/1.49  sat_guarded_non_collapsed_types:        0
% 7.32/1.49  num_pure_diseq_elim:                    0
% 7.32/1.49  simp_replaced_by:                       0
% 7.32/1.49  res_preprocessed:                       132
% 7.32/1.49  prep_upred:                             0
% 7.32/1.49  prep_unflattend:                        61
% 7.32/1.49  smt_new_axioms:                         0
% 7.32/1.49  pred_elim_cands:                        5
% 7.32/1.49  pred_elim:                              6
% 7.32/1.49  pred_elim_cl:                           9
% 7.32/1.49  pred_elim_cycles:                       9
% 7.32/1.49  merged_defs:                            0
% 7.32/1.49  merged_defs_ncl:                        0
% 7.32/1.49  bin_hyper_res:                          0
% 7.32/1.49  prep_cycles:                            4
% 7.32/1.49  pred_elim_time:                         0.015
% 7.32/1.49  splitting_time:                         0.
% 7.32/1.49  sem_filter_time:                        0.
% 7.32/1.49  monotx_time:                            0.
% 7.32/1.49  subtype_inf_time:                       0.
% 7.32/1.49  
% 7.32/1.49  ------ Problem properties
% 7.32/1.49  
% 7.32/1.49  clauses:                                24
% 7.32/1.49  conjectures:                            3
% 7.32/1.49  epr:                                    4
% 7.32/1.49  horn:                                   19
% 7.32/1.49  ground:                                 11
% 7.32/1.49  unary:                                  7
% 7.32/1.49  binary:                                 5
% 7.32/1.49  lits:                                   70
% 7.32/1.49  lits_eq:                                21
% 7.32/1.49  fd_pure:                                0
% 7.32/1.49  fd_pseudo:                              0
% 7.32/1.49  fd_cond:                                0
% 7.32/1.49  fd_pseudo_cond:                         1
% 7.32/1.49  ac_symbols:                             0
% 7.32/1.49  
% 7.32/1.49  ------ Propositional Solver
% 7.32/1.49  
% 7.32/1.49  prop_solver_calls:                      33
% 7.32/1.49  prop_fast_solver_calls:                 3437
% 7.32/1.49  smt_solver_calls:                       0
% 7.32/1.49  smt_fast_solver_calls:                  0
% 7.32/1.49  prop_num_of_clauses:                    4895
% 7.32/1.49  prop_preprocess_simplified:             8663
% 7.32/1.49  prop_fo_subsumed:                       409
% 7.32/1.49  prop_solver_time:                       0.
% 7.32/1.49  smt_solver_time:                        0.
% 7.32/1.49  smt_fast_solver_time:                   0.
% 7.32/1.49  prop_fast_solver_time:                  0.
% 7.32/1.49  prop_unsat_core_time:                   0.
% 7.32/1.49  
% 7.32/1.49  ------ QBF
% 7.32/1.49  
% 7.32/1.49  qbf_q_res:                              0
% 7.32/1.49  qbf_num_tautologies:                    0
% 7.32/1.49  qbf_prep_cycles:                        0
% 7.32/1.49  
% 7.32/1.49  ------ BMC1
% 7.32/1.49  
% 7.32/1.49  bmc1_current_bound:                     -1
% 7.32/1.49  bmc1_last_solved_bound:                 -1
% 7.32/1.49  bmc1_unsat_core_size:                   -1
% 7.32/1.49  bmc1_unsat_core_parents_size:           -1
% 7.32/1.49  bmc1_merge_next_fun:                    0
% 7.32/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.49  
% 7.32/1.49  ------ Instantiation
% 7.32/1.49  
% 7.32/1.49  inst_num_of_clauses:                    1344
% 7.32/1.49  inst_num_in_passive:                    394
% 7.32/1.49  inst_num_in_active:                     717
% 7.32/1.49  inst_num_in_unprocessed:                233
% 7.32/1.49  inst_num_of_loops:                      1190
% 7.32/1.49  inst_num_of_learning_restarts:          0
% 7.32/1.49  inst_num_moves_active_passive:          465
% 7.32/1.49  inst_lit_activity:                      0
% 7.32/1.49  inst_lit_activity_moves:                0
% 7.32/1.49  inst_num_tautologies:                   0
% 7.32/1.49  inst_num_prop_implied:                  0
% 7.32/1.49  inst_num_existing_simplified:           0
% 7.32/1.49  inst_num_eq_res_simplified:             0
% 7.32/1.49  inst_num_child_elim:                    0
% 7.32/1.49  inst_num_of_dismatching_blockings:      884
% 7.32/1.49  inst_num_of_non_proper_insts:           2740
% 7.32/1.49  inst_num_of_duplicates:                 0
% 7.32/1.49  inst_inst_num_from_inst_to_res:         0
% 7.32/1.49  inst_dismatching_checking_time:         0.
% 7.32/1.49  
% 7.32/1.49  ------ Resolution
% 7.32/1.49  
% 7.32/1.49  res_num_of_clauses:                     0
% 7.32/1.49  res_num_in_passive:                     0
% 7.32/1.49  res_num_in_active:                      0
% 7.32/1.49  res_num_of_loops:                       136
% 7.32/1.49  res_forward_subset_subsumed:            318
% 7.32/1.49  res_backward_subset_subsumed:           6
% 7.32/1.49  res_forward_subsumed:                   0
% 7.32/1.49  res_backward_subsumed:                  0
% 7.32/1.49  res_forward_subsumption_resolution:     0
% 7.32/1.49  res_backward_subsumption_resolution:    3
% 7.32/1.49  res_clause_to_clause_subsumption:       4536
% 7.32/1.49  res_orphan_elimination:                 0
% 7.32/1.49  res_tautology_del:                      322
% 7.32/1.49  res_num_eq_res_simplified:              0
% 7.32/1.49  res_num_sel_changes:                    0
% 7.32/1.49  res_moves_from_active_to_pass:          0
% 7.32/1.49  
% 7.32/1.49  ------ Superposition
% 7.32/1.49  
% 7.32/1.49  sup_time_total:                         0.
% 7.32/1.49  sup_time_generating:                    0.
% 7.32/1.49  sup_time_sim_full:                      0.
% 7.32/1.49  sup_time_sim_immed:                     0.
% 7.32/1.49  
% 7.32/1.49  sup_num_of_clauses:                     189
% 7.32/1.49  sup_num_in_active:                      75
% 7.32/1.49  sup_num_in_passive:                     114
% 7.32/1.49  sup_num_of_loops:                       237
% 7.32/1.49  sup_fw_superposition:                   412
% 7.32/1.49  sup_bw_superposition:                   441
% 7.32/1.49  sup_immediate_simplified:               327
% 7.32/1.49  sup_given_eliminated:                   0
% 7.32/1.49  comparisons_done:                       0
% 7.32/1.49  comparisons_avoided:                    582
% 7.32/1.49  
% 7.32/1.49  ------ Simplifications
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  sim_fw_subset_subsumed:                 94
% 7.32/1.49  sim_bw_subset_subsumed:                 72
% 7.32/1.49  sim_fw_subsumed:                        103
% 7.32/1.49  sim_bw_subsumed:                        10
% 7.32/1.49  sim_fw_subsumption_res:                 7
% 7.32/1.49  sim_bw_subsumption_res:                 2
% 7.32/1.49  sim_tautology_del:                      16
% 7.32/1.49  sim_eq_tautology_del:                   214
% 7.32/1.49  sim_eq_res_simp:                        5
% 7.32/1.49  sim_fw_demodulated:                     2
% 7.32/1.49  sim_bw_demodulated:                     133
% 7.32/1.49  sim_light_normalised:                   120
% 7.32/1.49  sim_joinable_taut:                      0
% 7.32/1.49  sim_joinable_simp:                      0
% 7.32/1.49  sim_ac_normalised:                      0
% 7.32/1.49  sim_smt_subsumption:                    0
% 7.32/1.49  
%------------------------------------------------------------------------------
