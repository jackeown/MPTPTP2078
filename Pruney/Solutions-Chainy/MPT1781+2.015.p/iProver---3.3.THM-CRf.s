%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:46 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  290 (25213 expanded)
%              Number of clauses        :  207 (6642 expanded)
%              Number of leaves         :   26 (7604 expanded)
%              Depth                    :   39
%              Number of atoms          : 1324 (224772 expanded)
%              Number of equality atoms :  660 (28859 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
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
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4)
        & ! [X3] :
            ( k1_funct_1(sK4,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK3))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
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
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    & ! [X3] :
        ( k1_funct_1(sK4,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f51,f50,f49])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1777,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_511,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_512,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_516,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_37,c_35])).

cnf(c_600,plain,
    ( m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_516])).

cnf(c_601,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_1771,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1781,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3625,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1781])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1787,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2526,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1771,c_1787])).

cnf(c_3629,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3625,c_2526])).

cnf(c_21,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_412,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_430,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_412])).

cnf(c_544,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_430,c_35])).

cnf(c_545,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_25,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_448,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_449,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_37,c_35])).

cnf(c_635,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_453])).

cnf(c_636,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_637,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_5157,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3629,c_37,c_545,c_637])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1775,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3624,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1781])).

cnf(c_2408,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1775,c_1787])).

cnf(c_3636,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3624,c_2408])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3881,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3636,c_37,c_44,c_545])).

cnf(c_5159,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5157,c_3881])).

cnf(c_18,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1779,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_466,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_467,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_471,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_37,c_35])).

cnf(c_614,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(X1)
    | k1_funct_1(k4_tmap_1(sK2,X1),X0) = X0
    | sK2 != sK2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_471])).

cnf(c_615,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_34])).

cnf(c_620,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(renaming,[status(thm)],[c_619])).

cnf(c_1769,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_3887,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3881,c_1769])).

cnf(c_4745,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_3887])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2051,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2221,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2051])).

cnf(c_2222,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2221])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2281,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2282,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2281])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1790,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3783,plain,
    ( m1_subset_1(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1790])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_552,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_553,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_37])).

cnf(c_558,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(X1)
    | sK2 != sK2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_558])).

cnf(c_583,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_34])).

cnf(c_588,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_1772,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_3888,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3881,c_1772])).

cnf(c_4722,plain,
    ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3783,c_3888])).

cnf(c_6140,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4745,c_43,c_45,c_2222,c_2282,c_4722])).

cnf(c_6141,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6140])).

cnf(c_6153,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_6141])).

cnf(c_602,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_493,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_494,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k4_tmap_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_498,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v1_funct_1(k4_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_37,c_35])).

cnf(c_607,plain,
    ( v1_funct_1(k4_tmap_1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_498])).

cnf(c_608,plain,
    ( v1_funct_1(k4_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_609,plain,
    ( v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2224,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v1_relat_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2051])).

cnf(c_2225,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_2090,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2673,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ r1_tarski(sK4,sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_2674,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2673])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2762,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2763,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2762])).

cnf(c_7698,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6153,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,c_2674,c_2763])).

cnf(c_5165,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_1779])).

cnf(c_5272,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5165,c_5159])).

cnf(c_6447,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_602,c_609,c_2225,c_2282])).

cnf(c_6448,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6447])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1778,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6459,plain,
    ( k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),X1)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X1))
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_1778])).

cnf(c_7179,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),X1)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X1))
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6459,c_43,c_45,c_2222,c_2282])).

cnf(c_7180,plain,
    ( k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),X1)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X1))
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7179])).

cnf(c_7712,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7698,c_7180])).

cnf(c_15759,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7712,c_602,c_609,c_2225,c_2282])).

cnf(c_15760,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15759])).

cnf(c_15772,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_15760])).

cnf(c_15987,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15772,c_43,c_45,c_2222,c_2282])).

cnf(c_15988,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15987])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1792,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3059,plain,
    ( k1_relat_1(X0) = k1_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_1792])).

cnf(c_3218,plain,
    ( k1_relat_1(X0) = k1_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_3059])).

cnf(c_122,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1264,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1277,plain,
    ( X0 != X1
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_1271,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1284,plain,
    ( X0 != X1
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_3237,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | k1_relat_1(X0) = k1_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3218,c_122,c_1277,c_1284])).

cnf(c_3238,plain,
    ( k1_relat_1(X0) = k1_relat_1(X1)
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3237])).

cnf(c_16002,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(X0)
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15988,c_3238])).

cnf(c_16264,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_relat_1(X0) = k1_relat_1(sK4)
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16002,c_5159])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_885,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k4_tmap_1(sK2,sK3) != X0
    | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3))
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK3) != X1
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_886,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_885])).

cnf(c_1270,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_2120,plain,
    ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) != sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
    | sK4 != k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1259,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2182,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_1260,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2287,plain,
    ( k4_tmap_1(sK2,sK3) != X0
    | sK4 != X0
    | sK4 = k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_2933,plain,
    ( k4_tmap_1(sK2,sK3) != sK4
    | sK4 = k4_tmap_1(sK2,sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_4547,plain,
    ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) = sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_7706,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7698,c_1792])).

cnf(c_1791,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6458,plain,
    ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_1790])).

cnf(c_7064,plain,
    ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6458,c_3888])).

cnf(c_6460,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_3887])).

cnf(c_7315,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7064,c_6460])).

cnf(c_7558,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_7315])).

cnf(c_8296,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7558,c_43,c_45,c_2222,c_2282])).

cnf(c_5162,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_1778])).

cnf(c_5840,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5162,c_602,c_609,c_2225,c_2282])).

cnf(c_5841,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5840])).

cnf(c_8310,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8296,c_5841])).

cnf(c_15031,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8310,c_43,c_45,c_2222,c_2282])).

cnf(c_15040,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_15031])).

cnf(c_15950,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15040,c_43,c_45,c_2222,c_2282])).

cnf(c_15951,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15950])).

cnf(c_15967,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_15951])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2766,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2770,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2766])).

cnf(c_4821,plain,
    ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_8304,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8296,c_1792])).

cnf(c_9538,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8304,c_32,c_31,c_30,c_601,c_608,c_636,c_886,c_2120,c_2182,c_2933,c_4547])).

cnf(c_1261,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3969,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != X1
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_4820,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != X0
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3969])).

cnf(c_12227,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4820])).

cnf(c_12229,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12227])).

cnf(c_16516,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15967,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,c_2674,c_2763,c_2770,c_4821,c_5159,c_9538,c_12229])).

cnf(c_1780,plain,
    ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16610,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_16516,c_1780])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_funct_1(sK4,X0) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1776,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3894,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3881,c_1776])).

cnf(c_6461,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_3894])).

cnf(c_7316,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7064,c_6461])).

cnf(c_7349,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_7316])).

cnf(c_7507,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7349,c_43,c_45,c_2222,c_2282])).

cnf(c_7519,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7507,c_5841])).

cnf(c_12106,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7519,c_43,c_45,c_2222,c_2282])).

cnf(c_12115,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_12106])).

cnf(c_12152,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12115,c_43,c_45,c_2222,c_2282])).

cnf(c_12153,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12152])).

cnf(c_12166,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_12153])).

cnf(c_7515,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7507,c_1792])).

cnf(c_8037,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7515,c_32,c_31,c_30,c_601,c_608,c_636,c_886,c_2120,c_2182,c_2933,c_4547])).

cnf(c_12585,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12166,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,c_2674,c_2763,c_2770,c_4821,c_5159,c_8037,c_12229])).

cnf(c_16611,plain,
    ( sK1(k4_tmap_1(sK2,sK3),sK4) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16610,c_5159,c_12585])).

cnf(c_16612,plain,
    ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16611])).

cnf(c_16669,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16264,c_32,c_43,c_31,c_30,c_45,c_601,c_602,c_608,c_609,c_636,c_886,c_2120,c_2182,c_2222,c_2225,c_2282,c_2674,c_2763,c_2933,c_4547,c_7706,c_16612])).

cnf(c_16731,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_16669,c_1780])).

cnf(c_16732,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16731,c_5159])).

cnf(c_5917,plain,
    ( v1_relat_1(X0) != iProver_top
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4722,c_43,c_45,c_2222,c_2282])).

cnf(c_5918,plain,
    ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5917])).

cnf(c_4085,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_3894])).

cnf(c_4304,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4085,c_43,c_45,c_2222,c_2282])).

cnf(c_4305,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4304])).

cnf(c_5928,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5918,c_4305])).

cnf(c_5940,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_5928])).

cnf(c_7644,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5940,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,c_2674,c_2763])).

cnf(c_7652,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7644,c_1792])).

cnf(c_2284,plain,
    ( ~ r1_tarski(k4_tmap_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | sK4 = k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2285,plain,
    ( sK4 = k4_tmap_1(sK2,sK3)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2284])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16732,c_16612,c_7652,c_4547,c_2933,c_2763,c_2674,c_2285,c_2282,c_2225,c_2222,c_2182,c_2120,c_886,c_636,c_609,c_608,c_602,c_601,c_45,c_30,c_31,c_43,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:44:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.99  
% 3.97/0.99  ------  iProver source info
% 3.97/0.99  
% 3.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.99  git: non_committed_changes: false
% 3.97/0.99  git: last_make_outside_of_git: false
% 3.97/0.99  
% 3.97/0.99  ------ 
% 3.97/0.99  
% 3.97/0.99  ------ Input Options
% 3.97/0.99  
% 3.97/0.99  --out_options                           all
% 3.97/0.99  --tptp_safe_out                         true
% 3.97/0.99  --problem_path                          ""
% 3.97/0.99  --include_path                          ""
% 3.97/0.99  --clausifier                            res/vclausify_rel
% 3.97/0.99  --clausifier_options                    --mode clausify
% 3.97/0.99  --stdin                                 false
% 3.97/0.99  --stats_out                             all
% 3.97/0.99  
% 3.97/0.99  ------ General Options
% 3.97/0.99  
% 3.97/0.99  --fof                                   false
% 3.97/0.99  --time_out_real                         305.
% 3.97/0.99  --time_out_virtual                      -1.
% 3.97/0.99  --symbol_type_check                     false
% 3.97/0.99  --clausify_out                          false
% 3.97/0.99  --sig_cnt_out                           false
% 3.97/0.99  --trig_cnt_out                          false
% 3.97/0.99  --trig_cnt_out_tolerance                1.
% 3.97/0.99  --trig_cnt_out_sk_spl                   false
% 3.97/0.99  --abstr_cl_out                          false
% 3.97/0.99  
% 3.97/0.99  ------ Global Options
% 3.97/0.99  
% 3.97/0.99  --schedule                              default
% 3.97/0.99  --add_important_lit                     false
% 3.97/0.99  --prop_solver_per_cl                    1000
% 3.97/0.99  --min_unsat_core                        false
% 3.97/0.99  --soft_assumptions                      false
% 3.97/0.99  --soft_lemma_size                       3
% 3.97/0.99  --prop_impl_unit_size                   0
% 3.97/0.99  --prop_impl_unit                        []
% 3.97/0.99  --share_sel_clauses                     true
% 3.97/0.99  --reset_solvers                         false
% 3.97/0.99  --bc_imp_inh                            [conj_cone]
% 3.97/0.99  --conj_cone_tolerance                   3.
% 3.97/0.99  --extra_neg_conj                        none
% 3.97/0.99  --large_theory_mode                     true
% 3.97/0.99  --prolific_symb_bound                   200
% 3.97/0.99  --lt_threshold                          2000
% 3.97/0.99  --clause_weak_htbl                      true
% 3.97/0.99  --gc_record_bc_elim                     false
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing Options
% 3.97/0.99  
% 3.97/0.99  --preprocessing_flag                    true
% 3.97/0.99  --time_out_prep_mult                    0.1
% 3.97/0.99  --splitting_mode                        input
% 3.97/0.99  --splitting_grd                         true
% 3.97/0.99  --splitting_cvd                         false
% 3.97/0.99  --splitting_cvd_svl                     false
% 3.97/0.99  --splitting_nvd                         32
% 3.97/0.99  --sub_typing                            true
% 3.97/0.99  --prep_gs_sim                           true
% 3.97/0.99  --prep_unflatten                        true
% 3.97/0.99  --prep_res_sim                          true
% 3.97/0.99  --prep_upred                            true
% 3.97/0.99  --prep_sem_filter                       exhaustive
% 3.97/0.99  --prep_sem_filter_out                   false
% 3.97/0.99  --pred_elim                             true
% 3.97/0.99  --res_sim_input                         true
% 3.97/0.99  --eq_ax_congr_red                       true
% 3.97/0.99  --pure_diseq_elim                       true
% 3.97/0.99  --brand_transform                       false
% 3.97/0.99  --non_eq_to_eq                          false
% 3.97/0.99  --prep_def_merge                        true
% 3.97/0.99  --prep_def_merge_prop_impl              false
% 3.97/0.99  --prep_def_merge_mbd                    true
% 3.97/0.99  --prep_def_merge_tr_red                 false
% 3.97/0.99  --prep_def_merge_tr_cl                  false
% 3.97/0.99  --smt_preprocessing                     true
% 3.97/0.99  --smt_ac_axioms                         fast
% 3.97/0.99  --preprocessed_out                      false
% 3.97/0.99  --preprocessed_stats                    false
% 3.97/0.99  
% 3.97/0.99  ------ Abstraction refinement Options
% 3.97/0.99  
% 3.97/0.99  --abstr_ref                             []
% 3.97/0.99  --abstr_ref_prep                        false
% 3.97/0.99  --abstr_ref_until_sat                   false
% 3.97/0.99  --abstr_ref_sig_restrict                funpre
% 3.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.99  --abstr_ref_under                       []
% 3.97/0.99  
% 3.97/0.99  ------ SAT Options
% 3.97/0.99  
% 3.97/0.99  --sat_mode                              false
% 3.97/0.99  --sat_fm_restart_options                ""
% 3.97/0.99  --sat_gr_def                            false
% 3.97/0.99  --sat_epr_types                         true
% 3.97/0.99  --sat_non_cyclic_types                  false
% 3.97/0.99  --sat_finite_models                     false
% 3.97/0.99  --sat_fm_lemmas                         false
% 3.97/0.99  --sat_fm_prep                           false
% 3.97/0.99  --sat_fm_uc_incr                        true
% 3.97/0.99  --sat_out_model                         small
% 3.97/0.99  --sat_out_clauses                       false
% 3.97/0.99  
% 3.97/0.99  ------ QBF Options
% 3.97/0.99  
% 3.97/0.99  --qbf_mode                              false
% 3.97/0.99  --qbf_elim_univ                         false
% 3.97/0.99  --qbf_dom_inst                          none
% 3.97/0.99  --qbf_dom_pre_inst                      false
% 3.97/0.99  --qbf_sk_in                             false
% 3.97/0.99  --qbf_pred_elim                         true
% 3.97/0.99  --qbf_split                             512
% 3.97/0.99  
% 3.97/0.99  ------ BMC1 Options
% 3.97/0.99  
% 3.97/0.99  --bmc1_incremental                      false
% 3.97/0.99  --bmc1_axioms                           reachable_all
% 3.97/0.99  --bmc1_min_bound                        0
% 3.97/0.99  --bmc1_max_bound                        -1
% 3.97/0.99  --bmc1_max_bound_default                -1
% 3.97/0.99  --bmc1_symbol_reachability              true
% 3.97/0.99  --bmc1_property_lemmas                  false
% 3.97/0.99  --bmc1_k_induction                      false
% 3.97/0.99  --bmc1_non_equiv_states                 false
% 3.97/0.99  --bmc1_deadlock                         false
% 3.97/0.99  --bmc1_ucm                              false
% 3.97/0.99  --bmc1_add_unsat_core                   none
% 3.97/0.99  --bmc1_unsat_core_children              false
% 3.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.99  --bmc1_out_stat                         full
% 3.97/0.99  --bmc1_ground_init                      false
% 3.97/0.99  --bmc1_pre_inst_next_state              false
% 3.97/0.99  --bmc1_pre_inst_state                   false
% 3.97/0.99  --bmc1_pre_inst_reach_state             false
% 3.97/0.99  --bmc1_out_unsat_core                   false
% 3.97/0.99  --bmc1_aig_witness_out                  false
% 3.97/0.99  --bmc1_verbose                          false
% 3.97/0.99  --bmc1_dump_clauses_tptp                false
% 3.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.99  --bmc1_dump_file                        -
% 3.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.99  --bmc1_ucm_extend_mode                  1
% 3.97/0.99  --bmc1_ucm_init_mode                    2
% 3.97/0.99  --bmc1_ucm_cone_mode                    none
% 3.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.99  --bmc1_ucm_relax_model                  4
% 3.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.99  --bmc1_ucm_layered_model                none
% 3.97/0.99  --bmc1_ucm_max_lemma_size               10
% 3.97/0.99  
% 3.97/0.99  ------ AIG Options
% 3.97/0.99  
% 3.97/0.99  --aig_mode                              false
% 3.97/0.99  
% 3.97/0.99  ------ Instantiation Options
% 3.97/0.99  
% 3.97/0.99  --instantiation_flag                    true
% 3.97/0.99  --inst_sos_flag                         false
% 3.97/0.99  --inst_sos_phase                        true
% 3.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.99  --inst_lit_sel_side                     num_symb
% 3.97/0.99  --inst_solver_per_active                1400
% 3.97/0.99  --inst_solver_calls_frac                1.
% 3.97/0.99  --inst_passive_queue_type               priority_queues
% 3.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.99  --inst_passive_queues_freq              [25;2]
% 3.97/0.99  --inst_dismatching                      true
% 3.97/0.99  --inst_eager_unprocessed_to_passive     true
% 3.97/0.99  --inst_prop_sim_given                   true
% 3.97/0.99  --inst_prop_sim_new                     false
% 3.97/0.99  --inst_subs_new                         false
% 3.97/0.99  --inst_eq_res_simp                      false
% 3.97/0.99  --inst_subs_given                       false
% 3.97/0.99  --inst_orphan_elimination               true
% 3.97/0.99  --inst_learning_loop_flag               true
% 3.97/0.99  --inst_learning_start                   3000
% 3.97/0.99  --inst_learning_factor                  2
% 3.97/0.99  --inst_start_prop_sim_after_learn       3
% 3.97/0.99  --inst_sel_renew                        solver
% 3.97/0.99  --inst_lit_activity_flag                true
% 3.97/0.99  --inst_restr_to_given                   false
% 3.97/0.99  --inst_activity_threshold               500
% 3.97/0.99  --inst_out_proof                        true
% 3.97/0.99  
% 3.97/0.99  ------ Resolution Options
% 3.97/0.99  
% 3.97/0.99  --resolution_flag                       true
% 3.97/0.99  --res_lit_sel                           adaptive
% 3.97/0.99  --res_lit_sel_side                      none
% 3.97/0.99  --res_ordering                          kbo
% 3.97/0.99  --res_to_prop_solver                    active
% 3.97/0.99  --res_prop_simpl_new                    false
% 3.97/0.99  --res_prop_simpl_given                  true
% 3.97/0.99  --res_passive_queue_type                priority_queues
% 3.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.99  --res_passive_queues_freq               [15;5]
% 3.97/0.99  --res_forward_subs                      full
% 3.97/0.99  --res_backward_subs                     full
% 3.97/0.99  --res_forward_subs_resolution           true
% 3.97/0.99  --res_backward_subs_resolution          true
% 3.97/0.99  --res_orphan_elimination                true
% 3.97/0.99  --res_time_limit                        2.
% 3.97/0.99  --res_out_proof                         true
% 3.97/0.99  
% 3.97/0.99  ------ Superposition Options
% 3.97/0.99  
% 3.97/0.99  --superposition_flag                    true
% 3.97/0.99  --sup_passive_queue_type                priority_queues
% 3.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.99  --demod_completeness_check              fast
% 3.97/0.99  --demod_use_ground                      true
% 3.97/0.99  --sup_to_prop_solver                    passive
% 3.97/0.99  --sup_prop_simpl_new                    true
% 3.97/0.99  --sup_prop_simpl_given                  true
% 3.97/0.99  --sup_fun_splitting                     false
% 3.97/0.99  --sup_smt_interval                      50000
% 3.97/0.99  
% 3.97/0.99  ------ Superposition Simplification Setup
% 3.97/0.99  
% 3.97/0.99  --sup_indices_passive                   []
% 3.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.99  --sup_full_bw                           [BwDemod]
% 3.97/0.99  --sup_immed_triv                        [TrivRules]
% 3.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.99  --sup_immed_bw_main                     []
% 3.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.99  
% 3.97/0.99  ------ Combination Options
% 3.97/0.99  
% 3.97/0.99  --comb_res_mult                         3
% 3.97/0.99  --comb_sup_mult                         2
% 3.97/0.99  --comb_inst_mult                        10
% 3.97/0.99  
% 3.97/0.99  ------ Debug Options
% 3.97/0.99  
% 3.97/0.99  --dbg_backtrace                         false
% 3.97/0.99  --dbg_dump_prop_clauses                 false
% 3.97/0.99  --dbg_dump_prop_clauses_file            -
% 3.97/0.99  --dbg_out_stat                          false
% 3.97/0.99  ------ Parsing...
% 3.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.99  ------ Proving...
% 3.97/0.99  ------ Problem Properties 
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  clauses                                 30
% 3.97/0.99  conjectures                             4
% 3.97/0.99  EPR                                     4
% 3.97/0.99  Horn                                    24
% 3.97/0.99  unary                                   11
% 3.97/0.99  binary                                  3
% 3.97/0.99  lits                                    95
% 3.97/0.99  lits eq                                 20
% 3.97/0.99  fd_pure                                 0
% 3.97/0.99  fd_pseudo                               0
% 3.97/0.99  fd_cond                                 3
% 3.97/0.99  fd_pseudo_cond                          1
% 3.97/0.99  AC symbols                              0
% 3.97/0.99  
% 3.97/0.99  ------ Schedule dynamic 5 is on 
% 3.97/0.99  
% 3.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  ------ 
% 3.97/0.99  Current options:
% 3.97/0.99  ------ 
% 3.97/0.99  
% 3.97/0.99  ------ Input Options
% 3.97/0.99  
% 3.97/0.99  --out_options                           all
% 3.97/0.99  --tptp_safe_out                         true
% 3.97/0.99  --problem_path                          ""
% 3.97/0.99  --include_path                          ""
% 3.97/0.99  --clausifier                            res/vclausify_rel
% 3.97/0.99  --clausifier_options                    --mode clausify
% 3.97/0.99  --stdin                                 false
% 3.97/0.99  --stats_out                             all
% 3.97/0.99  
% 3.97/0.99  ------ General Options
% 3.97/0.99  
% 3.97/0.99  --fof                                   false
% 3.97/0.99  --time_out_real                         305.
% 3.97/0.99  --time_out_virtual                      -1.
% 3.97/0.99  --symbol_type_check                     false
% 3.97/0.99  --clausify_out                          false
% 3.97/0.99  --sig_cnt_out                           false
% 3.97/0.99  --trig_cnt_out                          false
% 3.97/0.99  --trig_cnt_out_tolerance                1.
% 3.97/0.99  --trig_cnt_out_sk_spl                   false
% 3.97/0.99  --abstr_cl_out                          false
% 3.97/0.99  
% 3.97/0.99  ------ Global Options
% 3.97/0.99  
% 3.97/0.99  --schedule                              default
% 3.97/0.99  --add_important_lit                     false
% 3.97/0.99  --prop_solver_per_cl                    1000
% 3.97/0.99  --min_unsat_core                        false
% 3.97/0.99  --soft_assumptions                      false
% 3.97/0.99  --soft_lemma_size                       3
% 3.97/0.99  --prop_impl_unit_size                   0
% 3.97/0.99  --prop_impl_unit                        []
% 3.97/0.99  --share_sel_clauses                     true
% 3.97/0.99  --reset_solvers                         false
% 3.97/0.99  --bc_imp_inh                            [conj_cone]
% 3.97/0.99  --conj_cone_tolerance                   3.
% 3.97/0.99  --extra_neg_conj                        none
% 3.97/0.99  --large_theory_mode                     true
% 3.97/0.99  --prolific_symb_bound                   200
% 3.97/0.99  --lt_threshold                          2000
% 3.97/0.99  --clause_weak_htbl                      true
% 3.97/0.99  --gc_record_bc_elim                     false
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing Options
% 3.97/0.99  
% 3.97/0.99  --preprocessing_flag                    true
% 3.97/0.99  --time_out_prep_mult                    0.1
% 3.97/0.99  --splitting_mode                        input
% 3.97/0.99  --splitting_grd                         true
% 3.97/0.99  --splitting_cvd                         false
% 3.97/0.99  --splitting_cvd_svl                     false
% 3.97/0.99  --splitting_nvd                         32
% 3.97/0.99  --sub_typing                            true
% 3.97/0.99  --prep_gs_sim                           true
% 3.97/0.99  --prep_unflatten                        true
% 3.97/0.99  --prep_res_sim                          true
% 3.97/0.99  --prep_upred                            true
% 3.97/0.99  --prep_sem_filter                       exhaustive
% 3.97/0.99  --prep_sem_filter_out                   false
% 3.97/0.99  --pred_elim                             true
% 3.97/0.99  --res_sim_input                         true
% 3.97/0.99  --eq_ax_congr_red                       true
% 3.97/0.99  --pure_diseq_elim                       true
% 3.97/0.99  --brand_transform                       false
% 3.97/0.99  --non_eq_to_eq                          false
% 3.97/0.99  --prep_def_merge                        true
% 3.97/0.99  --prep_def_merge_prop_impl              false
% 3.97/0.99  --prep_def_merge_mbd                    true
% 3.97/0.99  --prep_def_merge_tr_red                 false
% 3.97/0.99  --prep_def_merge_tr_cl                  false
% 3.97/0.99  --smt_preprocessing                     true
% 3.97/0.99  --smt_ac_axioms                         fast
% 3.97/0.99  --preprocessed_out                      false
% 3.97/0.99  --preprocessed_stats                    false
% 3.97/0.99  
% 3.97/0.99  ------ Abstraction refinement Options
% 3.97/0.99  
% 3.97/0.99  --abstr_ref                             []
% 3.97/0.99  --abstr_ref_prep                        false
% 3.97/0.99  --abstr_ref_until_sat                   false
% 3.97/0.99  --abstr_ref_sig_restrict                funpre
% 3.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.99  --abstr_ref_under                       []
% 3.97/0.99  
% 3.97/0.99  ------ SAT Options
% 3.97/0.99  
% 3.97/0.99  --sat_mode                              false
% 3.97/0.99  --sat_fm_restart_options                ""
% 3.97/0.99  --sat_gr_def                            false
% 3.97/0.99  --sat_epr_types                         true
% 3.97/0.99  --sat_non_cyclic_types                  false
% 3.97/0.99  --sat_finite_models                     false
% 3.97/0.99  --sat_fm_lemmas                         false
% 3.97/0.99  --sat_fm_prep                           false
% 3.97/0.99  --sat_fm_uc_incr                        true
% 3.97/0.99  --sat_out_model                         small
% 3.97/0.99  --sat_out_clauses                       false
% 3.97/0.99  
% 3.97/0.99  ------ QBF Options
% 3.97/0.99  
% 3.97/0.99  --qbf_mode                              false
% 3.97/0.99  --qbf_elim_univ                         false
% 3.97/0.99  --qbf_dom_inst                          none
% 3.97/0.99  --qbf_dom_pre_inst                      false
% 3.97/0.99  --qbf_sk_in                             false
% 3.97/0.99  --qbf_pred_elim                         true
% 3.97/0.99  --qbf_split                             512
% 3.97/0.99  
% 3.97/0.99  ------ BMC1 Options
% 3.97/0.99  
% 3.97/0.99  --bmc1_incremental                      false
% 3.97/0.99  --bmc1_axioms                           reachable_all
% 3.97/0.99  --bmc1_min_bound                        0
% 3.97/0.99  --bmc1_max_bound                        -1
% 3.97/0.99  --bmc1_max_bound_default                -1
% 3.97/0.99  --bmc1_symbol_reachability              true
% 3.97/0.99  --bmc1_property_lemmas                  false
% 3.97/0.99  --bmc1_k_induction                      false
% 3.97/0.99  --bmc1_non_equiv_states                 false
% 3.97/0.99  --bmc1_deadlock                         false
% 3.97/0.99  --bmc1_ucm                              false
% 3.97/0.99  --bmc1_add_unsat_core                   none
% 3.97/0.99  --bmc1_unsat_core_children              false
% 3.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.99  --bmc1_out_stat                         full
% 3.97/0.99  --bmc1_ground_init                      false
% 3.97/0.99  --bmc1_pre_inst_next_state              false
% 3.97/0.99  --bmc1_pre_inst_state                   false
% 3.97/0.99  --bmc1_pre_inst_reach_state             false
% 3.97/0.99  --bmc1_out_unsat_core                   false
% 3.97/0.99  --bmc1_aig_witness_out                  false
% 3.97/0.99  --bmc1_verbose                          false
% 3.97/0.99  --bmc1_dump_clauses_tptp                false
% 3.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.99  --bmc1_dump_file                        -
% 3.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.99  --bmc1_ucm_extend_mode                  1
% 3.97/0.99  --bmc1_ucm_init_mode                    2
% 3.97/0.99  --bmc1_ucm_cone_mode                    none
% 3.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.99  --bmc1_ucm_relax_model                  4
% 3.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.99  --bmc1_ucm_layered_model                none
% 3.97/0.99  --bmc1_ucm_max_lemma_size               10
% 3.97/0.99  
% 3.97/0.99  ------ AIG Options
% 3.97/0.99  
% 3.97/0.99  --aig_mode                              false
% 3.97/0.99  
% 3.97/0.99  ------ Instantiation Options
% 3.97/0.99  
% 3.97/0.99  --instantiation_flag                    true
% 3.97/0.99  --inst_sos_flag                         false
% 3.97/0.99  --inst_sos_phase                        true
% 3.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.99  --inst_lit_sel_side                     none
% 3.97/0.99  --inst_solver_per_active                1400
% 3.97/0.99  --inst_solver_calls_frac                1.
% 3.97/0.99  --inst_passive_queue_type               priority_queues
% 3.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.99  --inst_passive_queues_freq              [25;2]
% 3.97/0.99  --inst_dismatching                      true
% 3.97/0.99  --inst_eager_unprocessed_to_passive     true
% 3.97/0.99  --inst_prop_sim_given                   true
% 3.97/0.99  --inst_prop_sim_new                     false
% 3.97/0.99  --inst_subs_new                         false
% 3.97/0.99  --inst_eq_res_simp                      false
% 3.97/0.99  --inst_subs_given                       false
% 3.97/0.99  --inst_orphan_elimination               true
% 3.97/0.99  --inst_learning_loop_flag               true
% 3.97/0.99  --inst_learning_start                   3000
% 3.97/0.99  --inst_learning_factor                  2
% 3.97/0.99  --inst_start_prop_sim_after_learn       3
% 3.97/0.99  --inst_sel_renew                        solver
% 3.97/0.99  --inst_lit_activity_flag                true
% 3.97/0.99  --inst_restr_to_given                   false
% 3.97/0.99  --inst_activity_threshold               500
% 3.97/0.99  --inst_out_proof                        true
% 3.97/0.99  
% 3.97/0.99  ------ Resolution Options
% 3.97/0.99  
% 3.97/0.99  --resolution_flag                       false
% 3.97/0.99  --res_lit_sel                           adaptive
% 3.97/0.99  --res_lit_sel_side                      none
% 3.97/0.99  --res_ordering                          kbo
% 3.97/0.99  --res_to_prop_solver                    active
% 3.97/0.99  --res_prop_simpl_new                    false
% 3.97/0.99  --res_prop_simpl_given                  true
% 3.97/0.99  --res_passive_queue_type                priority_queues
% 3.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.99  --res_passive_queues_freq               [15;5]
% 3.97/0.99  --res_forward_subs                      full
% 3.97/0.99  --res_backward_subs                     full
% 3.97/0.99  --res_forward_subs_resolution           true
% 3.97/0.99  --res_backward_subs_resolution          true
% 3.97/0.99  --res_orphan_elimination                true
% 3.97/0.99  --res_time_limit                        2.
% 3.97/0.99  --res_out_proof                         true
% 3.97/0.99  
% 3.97/0.99  ------ Superposition Options
% 3.97/0.99  
% 3.97/0.99  --superposition_flag                    true
% 3.97/0.99  --sup_passive_queue_type                priority_queues
% 3.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.99  --demod_completeness_check              fast
% 3.97/0.99  --demod_use_ground                      true
% 3.97/0.99  --sup_to_prop_solver                    passive
% 3.97/0.99  --sup_prop_simpl_new                    true
% 3.97/0.99  --sup_prop_simpl_given                  true
% 3.97/0.99  --sup_fun_splitting                     false
% 3.97/0.99  --sup_smt_interval                      50000
% 3.97/0.99  
% 3.97/0.99  ------ Superposition Simplification Setup
% 3.97/0.99  
% 3.97/0.99  --sup_indices_passive                   []
% 3.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.99  --sup_full_bw                           [BwDemod]
% 3.97/0.99  --sup_immed_triv                        [TrivRules]
% 3.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.99  --sup_immed_bw_main                     []
% 3.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.99  
% 3.97/0.99  ------ Combination Options
% 3.97/0.99  
% 3.97/0.99  --comb_res_mult                         3
% 3.97/0.99  --comb_sup_mult                         2
% 3.97/0.99  --comb_inst_mult                        10
% 3.97/0.99  
% 3.97/0.99  ------ Debug Options
% 3.97/0.99  
% 3.97/0.99  --dbg_backtrace                         false
% 3.97/0.99  --dbg_dump_prop_clauses                 false
% 3.97/0.99  --dbg_dump_prop_clauses_file            -
% 3.97/0.99  --dbg_out_stat                          false
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  ------ Proving...
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  % SZS status Theorem for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  fof(f9,axiom,(
% 3.97/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f24,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.97/0.99    inference(ennf_transformation,[],[f9])).
% 3.97/0.99  
% 3.97/0.99  fof(f25,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.99    inference(flattening,[],[f24])).
% 3.97/0.99  
% 3.97/0.99  fof(f44,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.99    inference(nnf_transformation,[],[f25])).
% 3.97/0.99  
% 3.97/0.99  fof(f45,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.99    inference(flattening,[],[f44])).
% 3.97/0.99  
% 3.97/0.99  fof(f46,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.99    inference(rectify,[],[f45])).
% 3.97/0.99  
% 3.97/0.99  fof(f47,plain,(
% 3.97/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f48,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.97/0.99  
% 3.97/0.99  fof(f70,plain,(
% 3.97/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f48])).
% 3.97/0.99  
% 3.97/0.99  fof(f15,conjecture,(
% 3.97/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f16,negated_conjecture,(
% 3.97/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.97/0.99    inference(negated_conjecture,[],[f15])).
% 3.97/0.99  
% 3.97/0.99  fof(f35,plain,(
% 3.97/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.97/0.99    inference(ennf_transformation,[],[f16])).
% 3.97/0.99  
% 3.97/0.99  fof(f36,plain,(
% 3.97/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.97/0.99    inference(flattening,[],[f35])).
% 3.97/0.99  
% 3.97/0.99  fof(f51,plain,(
% 3.97/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f50,plain,(
% 3.97/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f49,plain,(
% 3.97/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f52,plain,(
% 3.97/0.99    ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f51,f50,f49])).
% 3.97/0.99  
% 3.97/0.99  fof(f85,plain,(
% 3.97/0.99    m1_pre_topc(sK3,sK2)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f13,axiom,(
% 3.97/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f31,plain,(
% 3.97/0.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.97/0.99    inference(ennf_transformation,[],[f13])).
% 3.97/0.99  
% 3.97/0.99  fof(f32,plain,(
% 3.97/0.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.97/0.99    inference(flattening,[],[f31])).
% 3.97/0.99  
% 3.97/0.99  fof(f79,plain,(
% 3.97/0.99    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f32])).
% 3.97/0.99  
% 3.97/0.99  fof(f82,plain,(
% 3.97/0.99    v2_pre_topc(sK2)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f81,plain,(
% 3.97/0.99    ~v2_struct_0(sK2)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f83,plain,(
% 3.97/0.99    l1_pre_topc(sK2)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f7,axiom,(
% 3.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f20,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.99    inference(ennf_transformation,[],[f7])).
% 3.97/0.99  
% 3.97/0.99  fof(f21,plain,(
% 3.97/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.99    inference(flattening,[],[f20])).
% 3.97/0.99  
% 3.97/0.99  fof(f39,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.99    inference(nnf_transformation,[],[f21])).
% 3.97/0.99  
% 3.97/0.99  fof(f61,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f39])).
% 3.97/0.99  
% 3.97/0.99  fof(f6,axiom,(
% 3.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f19,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.99    inference(ennf_transformation,[],[f6])).
% 3.97/0.99  
% 3.97/0.99  fof(f60,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f19])).
% 3.97/0.99  
% 3.97/0.99  fof(f10,axiom,(
% 3.97/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f26,plain,(
% 3.97/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.97/0.99    inference(ennf_transformation,[],[f10])).
% 3.97/0.99  
% 3.97/0.99  fof(f74,plain,(
% 3.97/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f26])).
% 3.97/0.99  
% 3.97/0.99  fof(f1,axiom,(
% 3.97/0.99    v1_xboole_0(k1_xboole_0)),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f53,plain,(
% 3.97/0.99    v1_xboole_0(k1_xboole_0)),
% 3.97/0.99    inference(cnf_transformation,[],[f1])).
% 3.97/0.99  
% 3.97/0.99  fof(f11,axiom,(
% 3.97/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f27,plain,(
% 3.97/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.97/0.99    inference(ennf_transformation,[],[f11])).
% 3.97/0.99  
% 3.97/0.99  fof(f28,plain,(
% 3.97/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.97/0.99    inference(flattening,[],[f27])).
% 3.97/0.99  
% 3.97/0.99  fof(f75,plain,(
% 3.97/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f28])).
% 3.97/0.99  
% 3.97/0.99  fof(f78,plain,(
% 3.97/0.99    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f32])).
% 3.97/0.99  
% 3.97/0.99  fof(f88,plain,(
% 3.97/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f87,plain,(
% 3.97/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f72,plain,(
% 3.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f48])).
% 3.97/0.99  
% 3.97/0.99  fof(f14,axiom,(
% 3.97/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f33,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.97/0.99    inference(ennf_transformation,[],[f14])).
% 3.97/0.99  
% 3.97/0.99  fof(f34,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.97/0.99    inference(flattening,[],[f33])).
% 3.97/0.99  
% 3.97/0.99  fof(f80,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f34])).
% 3.97/0.99  
% 3.97/0.99  fof(f84,plain,(
% 3.97/0.99    ~v2_struct_0(sK3)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f86,plain,(
% 3.97/0.99    v1_funct_1(sK4)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f4,axiom,(
% 3.97/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f18,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.97/0.99    inference(ennf_transformation,[],[f4])).
% 3.97/0.99  
% 3.97/0.99  fof(f58,plain,(
% 3.97/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f18])).
% 3.97/0.99  
% 3.97/0.99  fof(f5,axiom,(
% 3.97/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f59,plain,(
% 3.97/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f5])).
% 3.97/0.99  
% 3.97/0.99  fof(f3,axiom,(
% 3.97/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f17,plain,(
% 3.97/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.97/0.99    inference(ennf_transformation,[],[f3])).
% 3.97/0.99  
% 3.97/0.99  fof(f57,plain,(
% 3.97/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f17])).
% 3.97/0.99  
% 3.97/0.99  fof(f12,axiom,(
% 3.97/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f29,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.97/0.99    inference(ennf_transformation,[],[f12])).
% 3.97/0.99  
% 3.97/0.99  fof(f30,plain,(
% 3.97/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.97/0.99    inference(flattening,[],[f29])).
% 3.97/0.99  
% 3.97/0.99  fof(f76,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f30])).
% 3.97/0.99  
% 3.97/0.99  fof(f77,plain,(
% 3.97/0.99    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f32])).
% 3.97/0.99  
% 3.97/0.99  fof(f2,axiom,(
% 3.97/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f37,plain,(
% 3.97/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.99    inference(nnf_transformation,[],[f2])).
% 3.97/0.99  
% 3.97/0.99  fof(f38,plain,(
% 3.97/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.99    inference(flattening,[],[f37])).
% 3.97/0.99  
% 3.97/0.99  fof(f54,plain,(
% 3.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.97/0.99    inference(cnf_transformation,[],[f38])).
% 3.97/0.99  
% 3.97/0.99  fof(f92,plain,(
% 3.97/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.97/0.99    inference(equality_resolution,[],[f54])).
% 3.97/0.99  
% 3.97/0.99  fof(f71,plain,(
% 3.97/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f48])).
% 3.97/0.99  
% 3.97/0.99  fof(f56,plain,(
% 3.97/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f38])).
% 3.97/0.99  
% 3.97/0.99  fof(f8,axiom,(
% 3.97/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 3.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f22,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.97/0.99    inference(ennf_transformation,[],[f8])).
% 3.97/0.99  
% 3.97/0.99  fof(f23,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.97/0.99    inference(flattening,[],[f22])).
% 3.97/0.99  
% 3.97/0.99  fof(f40,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.97/0.99    inference(nnf_transformation,[],[f23])).
% 3.97/0.99  
% 3.97/0.99  fof(f41,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.97/0.99    inference(rectify,[],[f40])).
% 3.97/0.99  
% 3.97/0.99  fof(f42,plain,(
% 3.97/0.99    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f43,plain,(
% 3.97/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.97/0.99  
% 3.97/0.99  fof(f69,plain,(
% 3.97/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f43])).
% 3.97/0.99  
% 3.97/0.99  fof(f90,plain,(
% 3.97/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  fof(f73,plain,(
% 3.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f48])).
% 3.97/0.99  
% 3.97/0.99  fof(f89,plain,(
% 3.97/0.99    ( ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f52])).
% 3.97/0.99  
% 3.97/0.99  cnf(c_20,plain,
% 3.97/0.99      ( ~ r1_tarski(X0,X1)
% 3.97/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.97/0.99      | ~ v1_funct_1(X1)
% 3.97/0.99      | ~ v1_funct_1(X0)
% 3.97/0.99      | ~ v1_relat_1(X0)
% 3.97/0.99      | ~ v1_relat_1(X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1777,plain,
% 3.97/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.97/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.97/0.99      | v1_funct_1(X1) != iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_33,negated_conjecture,
% 3.97/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.97/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_24,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.97/0.99      | ~ v2_pre_topc(X1)
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | ~ l1_pre_topc(X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_36,negated_conjecture,
% 3.97/0.99      ( v2_pre_topc(sK2) ),
% 3.97/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_511,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | ~ l1_pre_topc(X1)
% 3.97/0.99      | sK2 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_512,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 3.97/0.99      | v2_struct_0(sK2)
% 3.97/0.99      | ~ l1_pre_topc(sK2) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_37,negated_conjecture,
% 3.97/0.99      ( ~ v2_struct_0(sK2) ),
% 3.97/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_35,negated_conjecture,
% 3.97/0.99      ( l1_pre_topc(sK2) ),
% 3.97/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_516,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_512,c_37,c_35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_600,plain,
% 3.97/0.99      ( m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 3.97/0.99      | sK2 != sK2
% 3.97/0.99      | sK3 != X0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_516]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_601,plain,
% 3.97/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_600]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1771,plain,
% 3.97/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_13,plain,
% 3.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.97/0.99      | k1_xboole_0 = X2 ),
% 3.97/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1781,plain,
% 3.97/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.97/0.99      | k1_xboole_0 = X1
% 3.97/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.97/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3625,plain,
% 3.97/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.97/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.97/0.99      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1771,c_1781]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_7,plain,
% 3.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1787,plain,
% 3.97/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.97/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2526,plain,
% 3.97/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1771,c_1787]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3629,plain,
% 3.97/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 3.97/0.99      | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.97/0.99      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_3625,c_2526]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_21,plain,
% 3.97/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_0,plain,
% 3.97/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_22,plain,
% 3.97/0.99      ( v2_struct_0(X0)
% 3.97/0.99      | ~ l1_struct_0(X0)
% 3.97/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.97/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_412,plain,
% 3.97/0.99      ( v2_struct_0(X0)
% 3.97/0.99      | ~ l1_struct_0(X0)
% 3.97/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_430,plain,
% 3.97/0.99      ( v2_struct_0(X0)
% 3.97/0.99      | ~ l1_pre_topc(X0)
% 3.97/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.97/0.99      inference(resolution,[status(thm)],[c_21,c_412]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_544,plain,
% 3.97/0.99      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK2 != X0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_430,c_35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_545,plain,
% 3.97/0.99      ( v2_struct_0(sK2) | u1_struct_0(sK2) != k1_xboole_0 ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_544]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_25,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.97/0.99      | ~ m1_pre_topc(X1,X0)
% 3.97/0.99      | ~ v2_pre_topc(X0)
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | ~ l1_pre_topc(X0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_448,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.97/0.99      | ~ m1_pre_topc(X1,X0)
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | ~ l1_pre_topc(X0)
% 3.97/0.99      | sK2 != X0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_449,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 3.97/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | v2_struct_0(sK2)
% 3.97/0.99      | ~ l1_pre_topc(sK2) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_453,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 3.97/0.99      | ~ m1_pre_topc(X0,sK2) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_449,c_37,c_35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_635,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 3.97/0.99      | sK2 != sK2
% 3.97/0.99      | sK3 != X0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_453]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_636,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_635]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_637,plain,
% 3.97/0.99      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_5157,plain,
% 3.97/0.99      ( k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_3629,c_37,c_545,c_637]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_30,negated_conjecture,
% 3.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.97/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1775,plain,
% 3.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3624,plain,
% 3.97/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = u1_struct_0(sK3)
% 3.97/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.97/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1775,c_1781]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2408,plain,
% 3.97/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1775,c_1787]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3636,plain,
% 3.97/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 3.97/0.99      | u1_struct_0(sK3) = k1_relat_1(sK4)
% 3.97/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_3624,c_2408]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_31,negated_conjecture,
% 3.97/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.97/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_44,plain,
% 3.97/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3881,plain,
% 3.97/0.99      ( u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_3636,c_37,c_44,c_545]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_5159,plain,
% 3.97/0.99      ( k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_5157,c_3881]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_18,plain,
% 3.97/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.97/0.99      | r1_tarski(X0,X1)
% 3.97/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.97/0.99      | ~ v1_funct_1(X1)
% 3.97/0.99      | ~ v1_funct_1(X0)
% 3.97/0.99      | ~ v1_relat_1(X0)
% 3.97/0.99      | ~ v1_relat_1(X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1779,plain,
% 3.97/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.97/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.97/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.97/0.99      | v1_funct_1(X1) != iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_27,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.97/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.97/0.99      | ~ v2_pre_topc(X1)
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | ~ l1_pre_topc(X1)
% 3.97/0.99      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 3.97/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_466,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.97/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | ~ l1_pre_topc(X1)
% 3.97/0.99      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
% 3.97/0.99      | sK2 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_467,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | ~ r2_hidden(X1,u1_struct_0(X0))
% 3.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | v2_struct_0(sK2)
% 3.97/0.99      | ~ l1_pre_topc(sK2)
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_466]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_471,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | ~ r2_hidden(X1,u1_struct_0(X0))
% 3.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_467,c_37,c_35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_614,plain,
% 3.97/0.99      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 3.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,X1),X0) = X0
% 3.97/0.99      | sK2 != sK2
% 3.97/0.99      | sK3 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_471]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_615,plain,
% 3.97/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(sK3)
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_614]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_34,negated_conjecture,
% 3.97/0.99      ( ~ v2_struct_0(sK3) ),
% 3.97/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_619,plain,
% 3.97/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_615,c_34]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_620,plain,
% 3.97/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 3.97/0.99      inference(renaming,[status(thm)],[c_619]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1769,plain,
% 3.97/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 3.97/0.99      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 3.97/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3887,plain,
% 3.97/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 3.97/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_3881,c_1769]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_4745,plain,
% 3.97/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/0.99      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.97/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top
% 3.97/0.99      | v1_funct_1(sK4) != iProver_top
% 3.97/0.99      | v1_relat_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1779,c_3887]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_32,negated_conjecture,
% 3.97/0.99      ( v1_funct_1(sK4) ),
% 3.97/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_43,plain,
% 3.97/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_45,plain,
% 3.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_5,plain,
% 3.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.97/0.99      | ~ v1_relat_1(X1)
% 3.97/0.99      | v1_relat_1(X0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2051,plain,
% 3.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.99      | v1_relat_1(X0)
% 3.97/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2221,plain,
% 3.97/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.97/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 3.97/0.99      | v1_relat_1(sK4) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_2051]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2222,plain,
% 3.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.97/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top
% 3.97/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2221]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6,plain,
% 3.97/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.97/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2281,plain,
% 3.97/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2282,plain,
% 3.97/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2281]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_4,plain,
% 3.97/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1790,plain,
% 3.97/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.97/0.99      | m1_subset_1(X0,X1) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3783,plain,
% 3.97/0.99      ( m1_subset_1(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.97/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.97/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.97/0.99      | v1_funct_1(X1) != iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1779,c_1790]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_23,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | ~ l1_pre_topc(X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_552,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.97/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | sK2 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_553,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.99      | m1_subset_1(X1,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(X0)
% 3.97/0.99      | v2_struct_0(sK2) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_552]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_557,plain,
% 3.97/0.99      ( v2_struct_0(X0)
% 3.97/0.99      | m1_subset_1(X1,u1_struct_0(sK2))
% 3.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.99      | ~ m1_pre_topc(X0,sK2) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_553,c_37]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_558,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.97/0.99      | m1_subset_1(X1,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(X0) ),
% 3.97/0.99      inference(renaming,[status(thm)],[c_557]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_582,plain,
% 3.97/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.97/0.99      | m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | sK2 != sK2
% 3.97/0.99      | sK3 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_558]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_583,plain,
% 3.97/0.99      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.97/0.99      | v2_struct_0(sK3) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_582]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_587,plain,
% 3.97/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.97/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_583,c_34]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_588,plain,
% 3.97/0.99      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.97/0.99      inference(renaming,[status(thm)],[c_587]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1772,plain,
% 3.97/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.97/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3888,plain,
% 3.97/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.97/0.99      | m1_subset_1(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_3881,c_1772]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_4722,plain,
% 3.97/0.99      ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
% 3.97/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top
% 3.97/0.99      | v1_funct_1(sK4) != iProver_top
% 3.97/0.99      | v1_relat_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_3783,c_3888]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6140,plain,
% 3.97/0.99      ( v1_relat_1(X0) != iProver_top
% 3.97/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_4745,c_43,c_45,c_2222,c_2282,c_4722]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6141,plain,
% 3.97/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.97/0.99      | v1_funct_1(X0) != iProver_top
% 3.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.99      inference(renaming,[status(thm)],[c_6140]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6153,plain,
% 3.97/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_5159,c_6141]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_602,plain,
% 3.97/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_26,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | ~ v2_pre_topc(X1)
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | ~ l1_pre_topc(X1)
% 3.97/0.99      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 3.97/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_493,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.97/0.99      | v2_struct_0(X1)
% 3.97/0.99      | ~ l1_pre_topc(X1)
% 3.97/0.99      | v1_funct_1(k4_tmap_1(X1,X0))
% 3.97/0.99      | sK2 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_494,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.97/0.99      | v2_struct_0(sK2)
% 3.97/0.99      | ~ l1_pre_topc(sK2)
% 3.97/0.99      | v1_funct_1(k4_tmap_1(sK2,X0)) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_493]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_498,plain,
% 3.97/0.99      ( ~ m1_pre_topc(X0,sK2) | v1_funct_1(k4_tmap_1(sK2,X0)) ),
% 3.97/0.99      inference(global_propositional_subsumption,
% 3.97/0.99                [status(thm)],
% 3.97/0.99                [c_494,c_37,c_35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_607,plain,
% 3.97/0.99      ( v1_funct_1(k4_tmap_1(sK2,X0)) | sK2 != sK2 | sK3 != X0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_498]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_608,plain,
% 3.97/0.99      ( v1_funct_1(k4_tmap_1(sK2,sK3)) ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_607]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_609,plain,
% 3.97/0.99      ( v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2224,plain,
% 3.97/0.99      ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.97/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3))
% 3.97/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_2051]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2225,plain,
% 3.97/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.97/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2090,plain,
% 3.97/0.99      ( ~ r1_tarski(X0,sK4)
% 3.97/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
% 3.97/0.99      | ~ v1_funct_1(X0)
% 3.97/0.99      | ~ v1_funct_1(sK4)
% 3.97/0.99      | ~ v1_relat_1(X0)
% 3.97/0.99      | ~ v1_relat_1(sK4) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2673,plain,
% 3.97/0.99      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 3.97/0.99      | ~ r1_tarski(sK4,sK4)
% 3.97/0.99      | ~ v1_funct_1(sK4)
% 3.97/0.99      | ~ v1_relat_1(sK4) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_2090]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2674,plain,
% 3.97/0.99      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top
% 3.97/0.99      | r1_tarski(sK4,sK4) != iProver_top
% 3.97/0.99      | v1_funct_1(sK4) != iProver_top
% 3.97/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2673]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3,plain,
% 3.97/0.99      ( r1_tarski(X0,X0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2762,plain,
% 3.97/0.99      ( r1_tarski(sK4,sK4) ),
% 3.97/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2763,plain,
% 3.97/0.99      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2762]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_7698,plain,
% 3.97/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_6153,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,
% 3.97/1.00                 c_2674,c_2763]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5165,plain,
% 3.97/1.00      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_5159,c_1779]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5272,plain,
% 3.97/1.00      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(light_normalisation,[status(thm)],[c_5165,c_5159]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6447,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_5272,c_602,c_609,c_2225,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6448,plain,
% 3.97/1.00      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_6447]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_19,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.97/1.00      | ~ r1_tarski(X1,X2)
% 3.97/1.00      | ~ v1_funct_1(X2)
% 3.97/1.00      | ~ v1_funct_1(X1)
% 3.97/1.00      | ~ v1_relat_1(X1)
% 3.97/1.00      | ~ v1_relat_1(X2)
% 3.97/1.00      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1778,plain,
% 3.97/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 3.97/1.00      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 3.97/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X2) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X2) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6459,plain,
% 3.97/1.00      ( k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),X1)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X1))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X1) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X1)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6448,c_1778]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7179,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),X1)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X1))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X1) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X1)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_6459,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7180,plain,
% 3.97/1.00      ( k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),X1)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X1))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X1) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X1)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_7179]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7712,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7698,c_7180]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15759,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_7712,c_602,c_609,c_2225,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15760,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_15759]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15772,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1777,c_15760]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15987,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_15772,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15988,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_15987]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1792,plain,
% 3.97/1.00      ( X0 = X1
% 3.97/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3059,plain,
% 3.97/1.00      ( k1_relat_1(X0) = k1_relat_1(X1)
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1777,c_1792]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3218,plain,
% 3.97/1.00      ( k1_relat_1(X0) = k1_relat_1(X1)
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.97/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1777,c_3059]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_122,plain,
% 3.97/1.00      ( X0 = X1
% 3.97/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1264,plain,
% 3.97/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1277,plain,
% 3.97/1.00      ( X0 != X1
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1271,plain,
% 3.97/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1284,plain,
% 3.97/1.00      ( X0 != X1
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3237,plain,
% 3.97/1.00      ( v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | k1_relat_1(X0) = k1_relat_1(X1)
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.97/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_3218,c_122,c_1277,c_1284]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3238,plain,
% 3.97/1.00      ( k1_relat_1(X0) = k1_relat_1(X1)
% 3.97/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_3237]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16002,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(X0)
% 3.97/1.00      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_15988,c_3238]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16264,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | k1_relat_1(X0) = k1_relat_1(sK4)
% 3.97/1.00      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(demodulation,[status(thm)],[c_16002,c_5159]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_14,plain,
% 3.97/1.00      ( r2_funct_2(X0,X1,X2,X3)
% 3.97/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.97/1.00      | ~ v1_funct_2(X3,X0,X1)
% 3.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.97/1.00      | ~ v1_funct_1(X3)
% 3.97/1.00      | ~ v1_funct_1(X2)
% 3.97/1.00      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_28,negated_conjecture,
% 3.97/1.00      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
% 3.97/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_885,plain,
% 3.97/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.97/1.00      | ~ v1_funct_2(X3,X1,X2)
% 3.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/1.00      | ~ v1_funct_1(X3)
% 3.97/1.00      | ~ v1_funct_1(X0)
% 3.97/1.00      | k4_tmap_1(sK2,sK3) != X0
% 3.97/1.00      | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3))
% 3.97/1.00      | u1_struct_0(sK2) != X2
% 3.97/1.00      | u1_struct_0(sK3) != X1
% 3.97/1.00      | sK4 != X3 ),
% 3.97/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_886,plain,
% 3.97/1.00      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 3.97/1.00      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 3.97/1.00      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.97/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.97/1.00      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 3.97/1.00      | ~ v1_funct_1(sK4)
% 3.97/1.00      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.97/1.00      inference(unflattening,[status(thm)],[c_885]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1270,plain,
% 3.97/1.00      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2120,plain,
% 3.97/1.00      ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) != sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
% 3.97/1.00      | sK4 != k4_tmap_1(sK2,sK3) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1270]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1259,plain,( X0 = X0 ),theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2182,plain,
% 3.97/1.00      ( sK4 = sK4 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1259]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1260,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2287,plain,
% 3.97/1.00      ( k4_tmap_1(sK2,sK3) != X0 | sK4 != X0 | sK4 = k4_tmap_1(sK2,sK3) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1260]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2933,plain,
% 3.97/1.00      ( k4_tmap_1(sK2,sK3) != sK4
% 3.97/1.00      | sK4 = k4_tmap_1(sK2,sK3)
% 3.97/1.00      | sK4 != sK4 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2287]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4547,plain,
% 3.97/1.00      ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) = sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1259]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7706,plain,
% 3.97/1.00      ( k4_tmap_1(sK2,sK3) = sK4
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7698,c_1792]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1791,plain,
% 3.97/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6458,plain,
% 3.97/1.00      ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6448,c_1790]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7064,plain,
% 3.97/1.00      ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6458,c_3888]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6460,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.97/1.00      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6448,c_3887]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7315,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7064,c_6460]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7558,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1791,c_7315]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_8296,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_7558,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5162,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_5159,c_1778]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5840,plain,
% 3.97/1.00      ( v1_relat_1(X1) != iProver_top
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_5162,c_602,c_609,c_2225,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5841,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_5840]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_8310,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_8296,c_5841]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15031,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_8310,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15040,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1779,c_15031]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15950,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_15040,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15951,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_15950]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15967,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_5159,c_15951]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_17,plain,
% 3.97/1.00      ( r1_tarski(X0,X1)
% 3.97/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.97/1.00      | ~ v1_funct_1(X1)
% 3.97/1.00      | ~ v1_funct_1(X0)
% 3.97/1.00      | ~ v1_relat_1(X0)
% 3.97/1.00      | ~ v1_relat_1(X1)
% 3.97/1.00      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2766,plain,
% 3.97/1.00      ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 3.97/1.00      | ~ v1_funct_1(sK4)
% 3.97/1.00      | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
% 3.97/1.00      | ~ v1_relat_1(sK4)
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2770,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2766]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4821,plain,
% 3.97/1.00      ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1259]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_8304,plain,
% 3.97/1.00      ( k4_tmap_1(sK2,sK3) = sK4
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_8296,c_1792]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_9538,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_8304,c_32,c_31,c_30,c_601,c_608,c_636,c_886,c_2120,
% 3.97/1.00                 c_2182,c_2933,c_4547]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1261,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3969,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | k1_relat_1(k4_tmap_1(sK2,sK3)) != X1
% 3.97/1.00      | k1_relat_1(sK4) != X0 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1261]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4820,plain,
% 3.97/1.00      ( ~ r1_tarski(k1_relat_1(sK4),X0)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | k1_relat_1(k4_tmap_1(sK2,sK3)) != X0
% 3.97/1.00      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_3969]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12227,plain,
% 3.97/1.00      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 3.97/1.00      | k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
% 3.97/1.00      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_4820]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12229,plain,
% 3.97/1.00      ( k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
% 3.97/1.00      | k1_relat_1(sK4) != k1_relat_1(sK4)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_12227]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16516,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_15967,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,
% 3.97/1.00                 c_2674,c_2763,c_2770,c_4821,c_5159,c_9538,c_12229]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1780,plain,
% 3.97/1.00      ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.97/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16610,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_16516,c_1780]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_29,negated_conjecture,
% 3.97/1.00      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.97/1.00      | k1_funct_1(sK4,X0) = X0 ),
% 3.97/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1776,plain,
% 3.97/1.00      ( k1_funct_1(sK4,X0) = X0
% 3.97/1.00      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 3.97/1.00      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3894,plain,
% 3.97/1.00      ( k1_funct_1(sK4,X0) = X0
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.97/1.00      inference(demodulation,[status(thm)],[c_3881,c_1776]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6461,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.97/1.00      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6448,c_3894]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7316,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7064,c_6461]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7349,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1791,c_7316]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7507,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_7349,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7519,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7507,c_5841]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12106,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_7519,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12115,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1779,c_12106]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12152,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_12115,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12153,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_12152]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12166,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_5159,c_12153]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7515,plain,
% 3.97/1.00      ( k4_tmap_1(sK2,sK3) = sK4
% 3.97/1.00      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7507,c_1792]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_8037,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_7515,c_32,c_31,c_30,c_601,c_608,c_636,c_886,c_2120,
% 3.97/1.00                 c_2182,c_2933,c_4547]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12585,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_12166,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,
% 3.97/1.00                 c_2674,c_2763,c_2770,c_4821,c_5159,c_8037,c_12229]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16611,plain,
% 3.97/1.00      ( sK1(k4_tmap_1(sK2,sK3),sK4) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(light_normalisation,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_16610,c_5159,c_12585]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16612,plain,
% 3.97/1.00      ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(equality_resolution_simp,[status(thm)],[c_16611]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16669,plain,
% 3.97/1.00      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_16264,c_32,c_43,c_31,c_30,c_45,c_601,c_602,c_608,
% 3.97/1.00                 c_609,c_636,c_886,c_2120,c_2182,c_2222,c_2225,c_2282,
% 3.97/1.00                 c_2674,c_2763,c_2933,c_4547,c_7706,c_16612]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16731,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_16669,c_1780]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16732,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(light_normalisation,[status(thm)],[c_16731,c_5159]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5917,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_4722,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5918,plain,
% 3.97/1.00      ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_5917]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4085,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/1.00      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_funct_1(sK4) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1779,c_3894]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4304,plain,
% 3.97/1.00      ( v1_relat_1(X0) != iProver_top
% 3.97/1.00      | k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/1.00      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_4085,c_43,c_45,c_2222,c_2282]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4305,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/1.00      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_4304]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5928,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,X0) = iProver_top
% 3.97/1.00      | v1_funct_1(X0) != iProver_top
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_5918,c_4305]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5940,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.97/1.00      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.97/1.00      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_5159,c_5928]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7644,plain,
% 3.97/1.00      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_5940,c_43,c_45,c_602,c_609,c_2222,c_2225,c_2282,
% 3.97/1.00                 c_2674,c_2763]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7652,plain,
% 3.97/1.00      ( k4_tmap_1(sK2,sK3) = sK4
% 3.97/1.00      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_7644,c_1792]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2284,plain,
% 3.97/1.00      ( ~ r1_tarski(k4_tmap_1(sK2,sK3),sK4)
% 3.97/1.00      | ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 3.97/1.00      | sK4 = k4_tmap_1(sK2,sK3) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2285,plain,
% 3.97/1.00      ( sK4 = k4_tmap_1(sK2,sK3)
% 3.97/1.00      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top
% 3.97/1.00      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2284]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(contradiction,plain,
% 3.97/1.00      ( $false ),
% 3.97/1.00      inference(minisat,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_16732,c_16612,c_7652,c_4547,c_2933,c_2763,c_2674,
% 3.97/1.00                 c_2285,c_2282,c_2225,c_2222,c_2182,c_2120,c_886,c_636,
% 3.97/1.00                 c_609,c_608,c_602,c_601,c_45,c_30,c_31,c_43,c_32]) ).
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  ------                               Statistics
% 3.97/1.00  
% 3.97/1.00  ------ General
% 3.97/1.00  
% 3.97/1.00  abstr_ref_over_cycles:                  0
% 3.97/1.00  abstr_ref_under_cycles:                 0
% 3.97/1.00  gc_basic_clause_elim:                   0
% 3.97/1.00  forced_gc_time:                         0
% 3.97/1.00  parsing_time:                           0.013
% 3.97/1.00  unif_index_cands_time:                  0.
% 3.97/1.00  unif_index_add_time:                    0.
% 3.97/1.00  orderings_time:                         0.
% 3.97/1.00  out_proof_time:                         0.021
% 3.97/1.00  total_time:                             0.503
% 3.97/1.00  num_of_symbols:                         57
% 3.97/1.00  num_of_terms:                           9383
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing
% 3.97/1.00  
% 3.97/1.00  num_of_splits:                          0
% 3.97/1.00  num_of_split_atoms:                     0
% 3.97/1.00  num_of_reused_defs:                     0
% 3.97/1.00  num_eq_ax_congr_red:                    19
% 3.97/1.00  num_of_sem_filtered_clauses:            1
% 3.97/1.00  num_of_subtypes:                        0
% 3.97/1.00  monotx_restored_types:                  0
% 3.97/1.00  sat_num_of_epr_types:                   0
% 3.97/1.00  sat_num_of_non_cyclic_types:            0
% 3.97/1.00  sat_guarded_non_collapsed_types:        0
% 3.97/1.00  num_pure_diseq_elim:                    0
% 3.97/1.00  simp_replaced_by:                       0
% 3.97/1.00  res_preprocessed:                       158
% 3.97/1.00  prep_upred:                             0
% 3.97/1.00  prep_unflattend:                        29
% 3.97/1.00  smt_new_axioms:                         0
% 3.97/1.00  pred_elim_cands:                        6
% 3.97/1.00  pred_elim:                              7
% 3.97/1.00  pred_elim_cl:                           7
% 3.97/1.00  pred_elim_cycles:                       10
% 3.97/1.00  merged_defs:                            0
% 3.97/1.00  merged_defs_ncl:                        0
% 3.97/1.00  bin_hyper_res:                          0
% 3.97/1.00  prep_cycles:                            4
% 3.97/1.00  pred_elim_time:                         0.014
% 3.97/1.00  splitting_time:                         0.
% 3.97/1.00  sem_filter_time:                        0.
% 3.97/1.00  monotx_time:                            0.001
% 3.97/1.00  subtype_inf_time:                       0.
% 3.97/1.00  
% 3.97/1.00  ------ Problem properties
% 3.97/1.00  
% 3.97/1.00  clauses:                                30
% 3.97/1.00  conjectures:                            4
% 3.97/1.00  epr:                                    4
% 3.97/1.00  horn:                                   24
% 3.97/1.00  ground:                                 9
% 3.97/1.00  unary:                                  11
% 3.97/1.00  binary:                                 3
% 3.97/1.00  lits:                                   95
% 3.97/1.00  lits_eq:                                20
% 3.97/1.00  fd_pure:                                0
% 3.97/1.00  fd_pseudo:                              0
% 3.97/1.00  fd_cond:                                3
% 3.97/1.00  fd_pseudo_cond:                         1
% 3.97/1.00  ac_symbols:                             0
% 3.97/1.00  
% 3.97/1.00  ------ Propositional Solver
% 3.97/1.00  
% 3.97/1.00  prop_solver_calls:                      32
% 3.97/1.00  prop_fast_solver_calls:                 2609
% 3.97/1.00  smt_solver_calls:                       0
% 3.97/1.00  smt_fast_solver_calls:                  0
% 3.97/1.00  prop_num_of_clauses:                    4042
% 3.97/1.00  prop_preprocess_simplified:             8656
% 3.97/1.00  prop_fo_subsumed:                       176
% 3.97/1.00  prop_solver_time:                       0.
% 3.97/1.00  smt_solver_time:                        0.
% 3.97/1.00  smt_fast_solver_time:                   0.
% 3.97/1.00  prop_fast_solver_time:                  0.
% 3.97/1.00  prop_unsat_core_time:                   0.
% 3.97/1.00  
% 3.97/1.00  ------ QBF
% 3.97/1.00  
% 3.97/1.00  qbf_q_res:                              0
% 3.97/1.00  qbf_num_tautologies:                    0
% 3.97/1.00  qbf_prep_cycles:                        0
% 3.97/1.00  
% 3.97/1.00  ------ BMC1
% 3.97/1.00  
% 3.97/1.00  bmc1_current_bound:                     -1
% 3.97/1.00  bmc1_last_solved_bound:                 -1
% 3.97/1.00  bmc1_unsat_core_size:                   -1
% 3.97/1.00  bmc1_unsat_core_parents_size:           -1
% 3.97/1.00  bmc1_merge_next_fun:                    0
% 3.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.97/1.00  
% 3.97/1.00  ------ Instantiation
% 3.97/1.00  
% 3.97/1.00  inst_num_of_clauses:                    1143
% 3.97/1.00  inst_num_in_passive:                    337
% 3.97/1.00  inst_num_in_active:                     775
% 3.97/1.00  inst_num_in_unprocessed:                31
% 3.97/1.00  inst_num_of_loops:                      810
% 3.97/1.00  inst_num_of_learning_restarts:          0
% 3.97/1.00  inst_num_moves_active_passive:          28
% 3.97/1.00  inst_lit_activity:                      0
% 3.97/1.00  inst_lit_activity_moves:                0
% 3.97/1.00  inst_num_tautologies:                   0
% 3.97/1.00  inst_num_prop_implied:                  0
% 3.97/1.00  inst_num_existing_simplified:           0
% 3.97/1.00  inst_num_eq_res_simplified:             0
% 3.97/1.00  inst_num_child_elim:                    0
% 3.97/1.00  inst_num_of_dismatching_blockings:      499
% 3.97/1.00  inst_num_of_non_proper_insts:           1506
% 3.97/1.00  inst_num_of_duplicates:                 0
% 3.97/1.00  inst_inst_num_from_inst_to_res:         0
% 3.97/1.00  inst_dismatching_checking_time:         0.
% 3.97/1.00  
% 3.97/1.00  ------ Resolution
% 3.97/1.00  
% 3.97/1.00  res_num_of_clauses:                     0
% 3.97/1.00  res_num_in_passive:                     0
% 3.97/1.00  res_num_in_active:                      0
% 3.97/1.00  res_num_of_loops:                       162
% 3.97/1.00  res_forward_subset_subsumed:            205
% 3.97/1.00  res_backward_subset_subsumed:           4
% 3.97/1.00  res_forward_subsumed:                   0
% 3.97/1.00  res_backward_subsumed:                  0
% 3.97/1.00  res_forward_subsumption_resolution:     0
% 3.97/1.00  res_backward_subsumption_resolution:    0
% 3.97/1.00  res_clause_to_clause_subsumption:       5092
% 3.97/1.00  res_orphan_elimination:                 0
% 3.97/1.00  res_tautology_del:                      76
% 3.97/1.00  res_num_eq_res_simplified:              0
% 3.97/1.00  res_num_sel_changes:                    0
% 3.97/1.00  res_moves_from_active_to_pass:          0
% 3.97/1.00  
% 3.97/1.00  ------ Superposition
% 3.97/1.00  
% 3.97/1.00  sup_time_total:                         0.
% 3.97/1.00  sup_time_generating:                    0.
% 3.97/1.00  sup_time_sim_full:                      0.
% 3.97/1.00  sup_time_sim_immed:                     0.
% 3.97/1.00  
% 3.97/1.00  sup_num_of_clauses:                     206
% 3.97/1.00  sup_num_in_active:                      127
% 3.97/1.00  sup_num_in_passive:                     79
% 3.97/1.00  sup_num_of_loops:                       160
% 3.97/1.00  sup_fw_superposition:                   304
% 3.97/1.00  sup_bw_superposition:                   277
% 3.97/1.00  sup_immediate_simplified:               242
% 3.97/1.00  sup_given_eliminated:                   0
% 3.97/1.00  comparisons_done:                       0
% 3.97/1.00  comparisons_avoided:                    119
% 3.97/1.00  
% 3.97/1.00  ------ Simplifications
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  sim_fw_subset_subsumed:                 68
% 3.97/1.00  sim_bw_subset_subsumed:                 10
% 3.97/1.00  sim_fw_subsumed:                        63
% 3.97/1.00  sim_bw_subsumed:                        0
% 3.97/1.00  sim_fw_subsumption_res:                 18
% 3.97/1.00  sim_bw_subsumption_res:                 0
% 3.97/1.00  sim_tautology_del:                      29
% 3.97/1.00  sim_eq_tautology_del:                   193
% 3.97/1.00  sim_eq_res_simp:                        1
% 3.97/1.00  sim_fw_demodulated:                     9
% 3.97/1.00  sim_bw_demodulated:                     27
% 3.97/1.00  sim_light_normalised:                   104
% 3.97/1.00  sim_joinable_taut:                      0
% 3.97/1.00  sim_joinable_simp:                      0
% 3.97/1.00  sim_ac_normalised:                      0
% 3.97/1.00  sim_smt_subsumption:                    0
% 3.97/1.00  
%------------------------------------------------------------------------------
