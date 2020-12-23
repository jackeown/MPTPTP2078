%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:52 EST 2020

% Result     : Theorem 23.25s
% Output     : CNFRefutation 23.25s
% Verified   : 
% Statistics : Number of formulae       :  288 (4444 expanded)
%              Number of clauses        :  177 (1213 expanded)
%              Number of leaves         :   37 (1306 expanded)
%              Depth                    :   27
%              Number of atoms          : 1102 (28865 expanded)
%              Number of equality atoms :  435 (2064 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK6,X0,X1)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK5)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK4,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v1_tdlat_3(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ~ v5_pre_topc(sK6,sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v1_tdlat_3(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f50,f76,f75,f74])).

fof(f125,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f77])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f102,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f77])).

fof(f130,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f77])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))))
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f126,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f77])).

fof(f123,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f77])).

fof(f128,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

fof(f131,plain,(
    ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f77])).

fof(f129,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f77])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f124,plain,(
    v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f77])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f67,f68])).

fof(f117,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v3_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v3_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f70])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f71,f72])).

fof(f120,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f116,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f57,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f27])).

fof(f95,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1985,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_51,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1949,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_24,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1976,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3305,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1949,c_1976])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1977,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3849,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(superposition,[status(thm)],[c_3305,c_1977])).

cnf(c_49,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1951,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_3304,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1951,c_1976])).

cnf(c_3646,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(superposition,[status(thm)],[c_3304,c_1977])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1954,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_4087,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3646,c_1954])).

cnf(c_4188,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3849,c_4087])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1964,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8887,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3646,c_1964])).

cnf(c_8897,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8887,c_3646])).

cnf(c_50,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_57,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_58,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_9628,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8897,c_57,c_58])).

cnf(c_9629,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9628])).

cnf(c_9644,plain,
    ( v1_funct_2(X0,u1_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,sK4,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3849,c_9629])).

cnf(c_9668,plain,
    ( v1_funct_2(X0,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,sK4,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9644,c_3849])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_54,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_56,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_9947,plain,
    ( v1_funct_2(X0,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,sK4,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9668,c_54,c_56])).

cnf(c_9961,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK6,sK4,sK5) = iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4188,c_9947])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_59,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_45,negated_conjecture,
    ( ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_62,plain,
    ( v5_pre_topc(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1953,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_4088,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3646,c_1953])).

cnf(c_4189,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3849,c_4088])).

cnf(c_10233,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK6),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9961,c_59,c_62,c_4189])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1987,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10238,plain,
    ( r1_tarski(sK1(sK4,sK5,sK6),k2_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10233,c_1987])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1982,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9258,plain,
    ( v1_xboole_0(k2_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4188,c_1982])).

cnf(c_52,negated_conjecture,
    ( v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_176,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_41,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2619,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_2978,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0),sK4)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_3539,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),sK4)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3540,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | v5_pre_topc(sK6,sK4,sK5)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | k2_struct_0(sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2632,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4591,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_2632])).

cnf(c_857,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3286,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(X1))
    | k2_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_6744,plain,
    ( v1_xboole_0(k2_struct_0(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_6745,plain,
    ( k2_struct_0(sK5) != k1_xboole_0
    | v1_xboole_0(k2_struct_0(sK5)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6744])).

cnf(c_9609,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9258,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_176,c_3539,c_3540,c_4591,c_6745])).

cnf(c_1995,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1990,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4388,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1995,c_1990])).

cnf(c_9615,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9609,c_4388])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1966,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,X2,X0) != iProver_top
    | v3_pre_topc(X3,X0) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,X3),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12336,plain,
    ( k2_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) != iProver_top
    | v3_pre_topc(X2,sK5) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3646,c_1966])).

cnf(c_12347,plain,
    ( k2_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) != iProver_top
    | v3_pre_topc(X2,sK5) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12336,c_3646])).

cnf(c_13803,plain,
    ( k2_struct_0(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12347,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_3539,c_3540,c_4591])).

cnf(c_17457,plain,
    ( r1_tarski(sK1(sK4,sK5,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10238,c_9615,c_13803])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1991,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17461,plain,
    ( sK1(sK4,sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17457,c_1991])).

cnf(c_13835,plain,
    ( u1_struct_0(sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13803,c_3646])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1965,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14167,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13835,c_1965])).

cnf(c_14223,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14167,c_13835])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_14224,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14223,c_7])).

cnf(c_873,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3467,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_873])).

cnf(c_5546,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK6) ),
    inference(resolution,[status(thm)],[c_3467,c_48])).

cnf(c_5547,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5546])).

cnf(c_5549,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5547])).

cnf(c_10846,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3646,c_1965])).

cnf(c_10856,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10846,c_3646])).

cnf(c_11233,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10856,c_57,c_58])).

cnf(c_11234,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11233])).

cnf(c_13812,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13803,c_11234])).

cnf(c_14011,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13812,c_7])).

cnf(c_858,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8056,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_858,c_6])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_12973,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | v5_pre_topc(sK6,sK4,sK5)
    | v3_pre_topc(sK0(sK4,sK5,sK6),sK5)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | k2_struct_0(sK5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_46])).

cnf(c_13658,plain,
    ( k2_struct_0(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12973,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_3539,c_3540,c_4591])).

cnf(c_42981,plain,
    ( r1_tarski(k2_struct_0(sK5),X0)
    | ~ r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_8056,c_13658])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_855,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8120,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_861,c_855])).

cnf(c_13682,plain,
    ( m1_subset_1(k2_struct_0(sK5),X0)
    | ~ m1_subset_1(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_13658,c_8120])).

cnf(c_16725,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(k2_struct_0(sK5),X0) ),
    inference(resolution,[status(thm)],[c_13682,c_13])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_18667,plain,
    ( r1_tarski(k2_struct_0(sK5),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_16725,c_12])).

cnf(c_44158,plain,
    ( r1_tarski(k2_struct_0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42981,c_4,c_18667])).

cnf(c_856,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6860,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_856,c_1])).

cnf(c_6872,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_856,c_855])).

cnf(c_19531,plain,
    ( k1_xboole_0 = k2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_6872,c_13658])).

cnf(c_41001,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK5))
    | ~ r1_tarski(k2_struct_0(sK5),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6860,c_19531])).

cnf(c_44208,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK5))
    | X0 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_44158,c_41001])).

cnf(c_45005,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK5))
    | v1_funct_1(X0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44208,c_873])).

cnf(c_45027,plain,
    ( r1_tarski(X0,k2_struct_0(sK5)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45005])).

cnf(c_860,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_8122,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_861,c_860])).

cnf(c_46685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_8122,c_13658])).

cnf(c_47396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_46685,c_855])).

cnf(c_50254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(X0,k2_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_47396,c_13])).

cnf(c_50257,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50254])).

cnf(c_87392,plain,
    ( l1_pre_topc(X1) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14224,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_176,c_3539,c_3540,c_4591,c_5549,c_6745,c_9258,c_14011,c_45027,c_50257])).

cnf(c_87393,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_87392])).

cnf(c_87410,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK4),k1_xboole_0) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK4,sK5) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17461,c_87393])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1979,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7585,plain,
    ( k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6,k2_struct_0(sK5)) = k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) ),
    inference(superposition,[status(thm)],[c_4188,c_1979])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1980,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4601,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4188,c_1980])).

cnf(c_7597,plain,
    ( k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6,k2_struct_0(sK5)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_7585,c_4601])).

cnf(c_17825,plain,
    ( k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7597,c_9615,c_13803])).

cnf(c_1981,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17827,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17825,c_1981])).

cnf(c_17828,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17827,c_7])).

cnf(c_155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_170,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_172,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_18196,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17828,c_157,c_172])).

cnf(c_44,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1956,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_38,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1962,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2156,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1956,c_1962])).

cnf(c_27971,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | v1_tdlat_3(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3849,c_2156])).

cnf(c_55,plain,
    ( v1_tdlat_3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_29504,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27971,c_55,c_56])).

cnf(c_29517,plain,
    ( v4_pre_topc(k1_relat_1(k1_xboole_0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18196,c_29504])).

cnf(c_26,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1974,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12851,plain,
    ( k2_pre_topc(sK4,X0) = X0
    | v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3849,c_1974])).

cnf(c_13136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | v4_pre_topc(X0,sK4) != iProver_top
    | k2_pre_topc(sK4,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12851,c_56])).

cnf(c_13137,plain,
    ( k2_pre_topc(sK4,X0) = X0
    | v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13136])).

cnf(c_18202,plain,
    ( k2_pre_topc(sK4,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
    | v4_pre_topc(k1_relat_1(k1_xboole_0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_18196,c_13137])).

cnf(c_29673,plain,
    ( k2_pre_topc(sK4,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_29517,c_18202])).

cnf(c_87417,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK4),k1_xboole_0) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK4,sK5) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_87410,c_3849,c_17825,c_29673])).

cnf(c_13834,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13803,c_4189])).

cnf(c_16005,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9615,c_13834])).

cnf(c_1955,plain,
    ( v5_pre_topc(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_16006,plain,
    ( v5_pre_topc(k1_xboole_0,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9615,c_1955])).

cnf(c_87902,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87417,c_54,c_56,c_157,c_172,c_16005,c_16006])).

cnf(c_87907,plain,
    ( v4_relat_1(k1_xboole_0,k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_87902])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1984,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2987,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1984])).

cnf(c_88104,plain,
    ( v4_relat_1(k1_xboole_0,k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87907,c_2987])).

cnf(c_17,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1983,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_88109,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_88104,c_1983])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.25/3.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.25/3.48  
% 23.25/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.25/3.48  
% 23.25/3.48  ------  iProver source info
% 23.25/3.48  
% 23.25/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.25/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.25/3.48  git: non_committed_changes: false
% 23.25/3.48  git: last_make_outside_of_git: false
% 23.25/3.48  
% 23.25/3.48  ------ 
% 23.25/3.48  ------ Parsing...
% 23.25/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.25/3.48  
% 23.25/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.25/3.48  
% 23.25/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.25/3.48  
% 23.25/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.25/3.48  ------ Proving...
% 23.25/3.48  ------ Problem Properties 
% 23.25/3.48  
% 23.25/3.48  
% 23.25/3.48  clauses                                 53
% 23.25/3.48  conjectures                             9
% 23.25/3.48  EPR                                     16
% 23.25/3.48  Horn                                    43
% 23.25/3.48  unary                                   18
% 23.25/3.48  binary                                  9
% 23.25/3.48  lits                                    188
% 23.25/3.48  lits eq                                 23
% 23.25/3.48  fd_pure                                 0
% 23.25/3.48  fd_pseudo                               0
% 23.25/3.48  fd_cond                                 2
% 23.25/3.48  fd_pseudo_cond                          2
% 23.25/3.48  AC symbols                              0
% 23.25/3.48  
% 23.25/3.48  ------ Input Options Time Limit: Unbounded
% 23.25/3.48  
% 23.25/3.48  
% 23.25/3.48  ------ 
% 23.25/3.48  Current options:
% 23.25/3.48  ------ 
% 23.25/3.48  
% 23.25/3.48  
% 23.25/3.48  
% 23.25/3.48  
% 23.25/3.48  ------ Proving...
% 23.25/3.48  
% 23.25/3.48  
% 23.25/3.48  % SZS status Theorem for theBenchmark.p
% 23.25/3.48  
% 23.25/3.48   Resolution empty clause
% 23.25/3.48  
% 23.25/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.25/3.48  
% 23.25/3.48  fof(f10,axiom,(
% 23.25/3.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f30,plain,(
% 23.25/3.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.25/3.48    inference(ennf_transformation,[],[f10])).
% 23.25/3.48  
% 23.25/3.48  fof(f56,plain,(
% 23.25/3.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.25/3.48    inference(nnf_transformation,[],[f30])).
% 23.25/3.48  
% 23.25/3.48  fof(f92,plain,(
% 23.25/3.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f56])).
% 23.25/3.48  
% 23.25/3.48  fof(f25,conjecture,(
% 23.25/3.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f26,negated_conjecture,(
% 23.25/3.48    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 23.25/3.48    inference(negated_conjecture,[],[f25])).
% 23.25/3.48  
% 23.25/3.48  fof(f49,plain,(
% 23.25/3.48    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 23.25/3.48    inference(ennf_transformation,[],[f26])).
% 23.25/3.48  
% 23.25/3.48  fof(f50,plain,(
% 23.25/3.48    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f49])).
% 23.25/3.48  
% 23.25/3.48  fof(f76,plain,(
% 23.25/3.48    ( ! [X0,X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK6,X0,X1) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f75,plain,(
% 23.25/3.48    ( ! [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,X0,sK5) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))) )),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f74,plain,(
% 23.25/3.48    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK4,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v1_tdlat_3(sK4) & v2_pre_topc(sK4))),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f77,plain,(
% 23.25/3.48    ((~v5_pre_topc(sK6,sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v1_tdlat_3(sK4) & v2_pre_topc(sK4)),
% 23.25/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f50,f76,f75,f74])).
% 23.25/3.48  
% 23.25/3.48  fof(f125,plain,(
% 23.25/3.48    l1_pre_topc(sK4)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f18,axiom,(
% 23.25/3.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f36,plain,(
% 23.25/3.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f18])).
% 23.25/3.48  
% 23.25/3.48  fof(f102,plain,(
% 23.25/3.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f36])).
% 23.25/3.48  
% 23.25/3.48  fof(f17,axiom,(
% 23.25/3.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f35,plain,(
% 23.25/3.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f17])).
% 23.25/3.48  
% 23.25/3.48  fof(f101,plain,(
% 23.25/3.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f35])).
% 23.25/3.48  
% 23.25/3.48  fof(f127,plain,(
% 23.25/3.48    l1_pre_topc(sK5)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f130,plain,(
% 23.25/3.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f21,axiom,(
% 23.25/3.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f41,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.25/3.48    inference(ennf_transformation,[],[f21])).
% 23.25/3.48  
% 23.25/3.48  fof(f42,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f41])).
% 23.25/3.48  
% 23.25/3.48  fof(f62,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(nnf_transformation,[],[f42])).
% 23.25/3.48  
% 23.25/3.48  fof(f63,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(rectify,[],[f62])).
% 23.25/3.48  
% 23.25/3.48  fof(f64,plain,(
% 23.25/3.48    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f65,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).
% 23.25/3.48  
% 23.25/3.48  fof(f114,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f65])).
% 23.25/3.48  
% 23.25/3.48  fof(f126,plain,(
% 23.25/3.48    v2_pre_topc(sK5)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f123,plain,(
% 23.25/3.48    v2_pre_topc(sK4)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f128,plain,(
% 23.25/3.48    v1_funct_1(sK6)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f131,plain,(
% 23.25/3.48    ~v5_pre_topc(sK6,sK4,sK5)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f129,plain,(
% 23.25/3.48    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f9,axiom,(
% 23.25/3.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f55,plain,(
% 23.25/3.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.25/3.48    inference(nnf_transformation,[],[f9])).
% 23.25/3.48  
% 23.25/3.48  fof(f90,plain,(
% 23.25/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.25/3.48    inference(cnf_transformation,[],[f55])).
% 23.25/3.48  
% 23.25/3.48  fof(f13,axiom,(
% 23.25/3.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f31,plain,(
% 23.25/3.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f13])).
% 23.25/3.48  
% 23.25/3.48  fof(f96,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f31])).
% 23.25/3.48  
% 23.25/3.48  fof(f124,plain,(
% 23.25/3.48    v1_tdlat_3(sK4)),
% 23.25/3.48    inference(cnf_transformation,[],[f77])).
% 23.25/3.48  
% 23.25/3.48  fof(f1,axiom,(
% 23.25/3.48    v1_xboole_0(k1_xboole_0)),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f78,plain,(
% 23.25/3.48    v1_xboole_0(k1_xboole_0)),
% 23.25/3.48    inference(cnf_transformation,[],[f1])).
% 23.25/3.48  
% 23.25/3.48  fof(f23,axiom,(
% 23.25/3.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f45,plain,(
% 23.25/3.48    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.25/3.48    inference(ennf_transformation,[],[f23])).
% 23.25/3.48  
% 23.25/3.48  fof(f46,plain,(
% 23.25/3.48    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f45])).
% 23.25/3.48  
% 23.25/3.48  fof(f66,plain,(
% 23.25/3.48    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(nnf_transformation,[],[f46])).
% 23.25/3.48  
% 23.25/3.48  fof(f67,plain,(
% 23.25/3.48    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(rectify,[],[f66])).
% 23.25/3.48  
% 23.25/3.48  fof(f68,plain,(
% 23.25/3.48    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f69,plain,(
% 23.25/3.48    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f67,f68])).
% 23.25/3.48  
% 23.25/3.48  fof(f117,plain,(
% 23.25/3.48    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f69])).
% 23.25/3.48  
% 23.25/3.48  fof(f20,axiom,(
% 23.25/3.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f39,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f20])).
% 23.25/3.48  
% 23.25/3.48  fof(f40,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f39])).
% 23.25/3.48  
% 23.25/3.48  fof(f58,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(nnf_transformation,[],[f40])).
% 23.25/3.48  
% 23.25/3.48  fof(f59,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(rectify,[],[f58])).
% 23.25/3.48  
% 23.25/3.48  fof(f60,plain,(
% 23.25/3.48    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f61,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).
% 23.25/3.48  
% 23.25/3.48  fof(f111,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f61])).
% 23.25/3.48  
% 23.25/3.48  fof(f14,axiom,(
% 23.25/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f32,plain,(
% 23.25/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.25/3.48    inference(ennf_transformation,[],[f14])).
% 23.25/3.48  
% 23.25/3.48  fof(f97,plain,(
% 23.25/3.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.25/3.48    inference(cnf_transformation,[],[f32])).
% 23.25/3.48  
% 23.25/3.48  fof(f5,axiom,(
% 23.25/3.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f29,plain,(
% 23.25/3.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f5])).
% 23.25/3.48  
% 23.25/3.48  fof(f84,plain,(
% 23.25/3.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f29])).
% 23.25/3.48  
% 23.25/3.48  fof(f105,plain,(
% 23.25/3.48    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f61])).
% 23.25/3.48  
% 23.25/3.48  fof(f4,axiom,(
% 23.25/3.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f28,plain,(
% 23.25/3.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 23.25/3.48    inference(ennf_transformation,[],[f4])).
% 23.25/3.48  
% 23.25/3.48  fof(f83,plain,(
% 23.25/3.48    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f28])).
% 23.25/3.48  
% 23.25/3.48  fof(f115,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f65])).
% 23.25/3.48  
% 23.25/3.48  fof(f6,axiom,(
% 23.25/3.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f53,plain,(
% 23.25/3.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.25/3.48    inference(nnf_transformation,[],[f6])).
% 23.25/3.48  
% 23.25/3.48  fof(f54,plain,(
% 23.25/3.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.25/3.48    inference(flattening,[],[f53])).
% 23.25/3.48  
% 23.25/3.48  fof(f87,plain,(
% 23.25/3.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 23.25/3.48    inference(cnf_transformation,[],[f54])).
% 23.25/3.48  
% 23.25/3.48  fof(f134,plain,(
% 23.25/3.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 23.25/3.48    inference(equality_resolution,[],[f87])).
% 23.25/3.48  
% 23.25/3.48  fof(f109,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f61])).
% 23.25/3.48  
% 23.25/3.48  fof(f3,axiom,(
% 23.25/3.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f82,plain,(
% 23.25/3.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f3])).
% 23.25/3.48  
% 23.25/3.48  fof(f91,plain,(
% 23.25/3.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f55])).
% 23.25/3.48  
% 23.25/3.48  fof(f2,axiom,(
% 23.25/3.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f51,plain,(
% 23.25/3.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.25/3.48    inference(nnf_transformation,[],[f2])).
% 23.25/3.48  
% 23.25/3.48  fof(f52,plain,(
% 23.25/3.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.25/3.48    inference(flattening,[],[f51])).
% 23.25/3.48  
% 23.25/3.48  fof(f81,plain,(
% 23.25/3.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f52])).
% 23.25/3.48  
% 23.25/3.48  fof(f16,axiom,(
% 23.25/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f34,plain,(
% 23.25/3.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.25/3.48    inference(ennf_transformation,[],[f16])).
% 23.25/3.48  
% 23.25/3.48  fof(f100,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.25/3.48    inference(cnf_transformation,[],[f34])).
% 23.25/3.48  
% 23.25/3.48  fof(f15,axiom,(
% 23.25/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f33,plain,(
% 23.25/3.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.25/3.48    inference(ennf_transformation,[],[f15])).
% 23.25/3.48  
% 23.25/3.48  fof(f98,plain,(
% 23.25/3.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.25/3.48    inference(cnf_transformation,[],[f33])).
% 23.25/3.48  
% 23.25/3.48  fof(f24,axiom,(
% 23.25/3.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f47,plain,(
% 23.25/3.48    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.25/3.48    inference(ennf_transformation,[],[f24])).
% 23.25/3.48  
% 23.25/3.48  fof(f48,plain,(
% 23.25/3.48    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f47])).
% 23.25/3.48  
% 23.25/3.48  fof(f70,plain,(
% 23.25/3.48    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(nnf_transformation,[],[f48])).
% 23.25/3.48  
% 23.25/3.48  fof(f71,plain,(
% 23.25/3.48    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(rectify,[],[f70])).
% 23.25/3.48  
% 23.25/3.48  fof(f72,plain,(
% 23.25/3.48    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.25/3.48    introduced(choice_axiom,[])).
% 23.25/3.48  
% 23.25/3.48  fof(f73,plain,(
% 23.25/3.48    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.25/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f71,f72])).
% 23.25/3.48  
% 23.25/3.48  fof(f120,plain,(
% 23.25/3.48    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f73])).
% 23.25/3.48  
% 23.25/3.48  fof(f22,axiom,(
% 23.25/3.48    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f43,plain,(
% 23.25/3.48    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f22])).
% 23.25/3.48  
% 23.25/3.48  fof(f44,plain,(
% 23.25/3.48    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f43])).
% 23.25/3.48  
% 23.25/3.48  fof(f116,plain,(
% 23.25/3.48    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f44])).
% 23.25/3.48  
% 23.25/3.48  fof(f19,axiom,(
% 23.25/3.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f37,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(ennf_transformation,[],[f19])).
% 23.25/3.48  
% 23.25/3.48  fof(f38,plain,(
% 23.25/3.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.25/3.48    inference(flattening,[],[f37])).
% 23.25/3.48  
% 23.25/3.48  fof(f103,plain,(
% 23.25/3.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f38])).
% 23.25/3.48  
% 23.25/3.48  fof(f11,axiom,(
% 23.25/3.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f94,plain,(
% 23.25/3.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.25/3.48    inference(cnf_transformation,[],[f11])).
% 23.25/3.48  
% 23.25/3.48  fof(f12,axiom,(
% 23.25/3.48    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 23.25/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.25/3.48  
% 23.25/3.48  fof(f27,plain,(
% 23.25/3.48    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 23.25/3.48    inference(pure_predicate_removal,[],[f12])).
% 23.25/3.48  
% 23.25/3.48  fof(f57,plain,(
% 23.25/3.48    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 23.25/3.48    inference(rectify,[],[f27])).
% 23.25/3.48  
% 23.25/3.48  fof(f95,plain,(
% 23.25/3.48    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 23.25/3.48    inference(cnf_transformation,[],[f57])).
% 23.25/3.48  
% 23.25/3.48  cnf(c_15,plain,
% 23.25/3.48      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 23.25/3.48      inference(cnf_transformation,[],[f92]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_1985,plain,
% 23.25/3.48      ( v4_relat_1(X0,X1) != iProver_top
% 23.25/3.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 23.25/3.48      | v1_relat_1(X0) != iProver_top ),
% 23.25/3.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_51,negated_conjecture,
% 23.25/3.48      ( l1_pre_topc(sK4) ),
% 23.25/3.48      inference(cnf_transformation,[],[f125]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_1949,plain,
% 23.25/3.48      ( l1_pre_topc(sK4) = iProver_top ),
% 23.25/3.48      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_24,plain,
% 23.25/3.48      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.25/3.48      inference(cnf_transformation,[],[f102]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_1976,plain,
% 23.25/3.48      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.25/3.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_3305,plain,
% 23.25/3.48      ( l1_struct_0(sK4) = iProver_top ),
% 23.25/3.48      inference(superposition,[status(thm)],[c_1949,c_1976]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_23,plain,
% 23.25/3.48      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 23.25/3.48      inference(cnf_transformation,[],[f101]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_1977,plain,
% 23.25/3.48      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 23.25/3.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_3849,plain,
% 23.25/3.48      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 23.25/3.48      inference(superposition,[status(thm)],[c_3305,c_1977]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_49,negated_conjecture,
% 23.25/3.48      ( l1_pre_topc(sK5) ),
% 23.25/3.48      inference(cnf_transformation,[],[f127]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_1951,plain,
% 23.25/3.48      ( l1_pre_topc(sK5) = iProver_top ),
% 23.25/3.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_3304,plain,
% 23.25/3.48      ( l1_struct_0(sK5) = iProver_top ),
% 23.25/3.48      inference(superposition,[status(thm)],[c_1951,c_1976]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_3646,plain,
% 23.25/3.48      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 23.25/3.48      inference(superposition,[status(thm)],[c_3304,c_1977]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_46,negated_conjecture,
% 23.25/3.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 23.25/3.48      inference(cnf_transformation,[],[f130]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_1954,plain,
% 23.25/3.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 23.25/3.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_4087,plain,
% 23.25/3.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
% 23.25/3.48      inference(demodulation,[status(thm)],[c_3646,c_1954]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_4188,plain,
% 23.25/3.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
% 23.25/3.48      inference(demodulation,[status(thm)],[c_3849,c_4087]) ).
% 23.25/3.48  
% 23.25/3.48  cnf(c_36,plain,
% 23.25/3.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.25/3.48      | v5_pre_topc(X0,X1,X2)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.25/3.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 23.25/3.49      | ~ v1_funct_1(X0)
% 23.25/3.49      | ~ v2_pre_topc(X1)
% 23.25/3.49      | ~ v2_pre_topc(X2)
% 23.25/3.49      | ~ l1_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X2) ),
% 23.25/3.49      inference(cnf_transformation,[],[f114]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1964,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,X2) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(X2) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X2) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_8887,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_3646,c_1964]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_8897,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_8887,c_3646]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_50,negated_conjecture,
% 23.25/3.49      ( v2_pre_topc(sK5) ),
% 23.25/3.49      inference(cnf_transformation,[],[f126]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_57,plain,
% 23.25/3.49      ( v2_pre_topc(sK5) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_58,plain,
% 23.25/3.49      ( l1_pre_topc(sK5) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9628,plain,
% 23.25/3.49      ( l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_8897,c_57,c_58]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9629,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(X1,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(renaming,[status(thm)],[c_9628]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9644,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,sK4,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(sK4,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK4) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_3849,c_9629]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9668,plain,
% 23.25/3.49      ( v1_funct_2(X0,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,sK4,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(sK4,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK4) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_9644,c_3849]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_53,negated_conjecture,
% 23.25/3.49      ( v2_pre_topc(sK4) ),
% 23.25/3.49      inference(cnf_transformation,[],[f123]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_54,plain,
% 23.25/3.49      ( v2_pre_topc(sK4) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_56,plain,
% 23.25/3.49      ( l1_pre_topc(sK4) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9947,plain,
% 23.25/3.49      ( v1_funct_2(X0,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,sK4,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(sK1(sK4,sK5,X0),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_9668,c_54,c_56]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9961,plain,
% 23.25/3.49      ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(sK6,sK4,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(sK1(sK4,sK5,sK6),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 23.25/3.49      | v1_funct_1(sK6) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_4188,c_9947]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_48,negated_conjecture,
% 23.25/3.49      ( v1_funct_1(sK6) ),
% 23.25/3.49      inference(cnf_transformation,[],[f128]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_59,plain,
% 23.25/3.49      ( v1_funct_1(sK6) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_45,negated_conjecture,
% 23.25/3.49      ( ~ v5_pre_topc(sK6,sK4,sK5) ),
% 23.25/3.49      inference(cnf_transformation,[],[f131]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_62,plain,
% 23.25/3.49      ( v5_pre_topc(sK6,sK4,sK5) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_47,negated_conjecture,
% 23.25/3.49      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 23.25/3.49      inference(cnf_transformation,[],[f129]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1953,plain,
% 23.25/3.49      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_4088,plain,
% 23.25/3.49      ( v1_funct_2(sK6,u1_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_3646,c_1953]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_4189,plain,
% 23.25/3.49      ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_3849,c_4088]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_10233,plain,
% 23.25/3.49      ( m1_subset_1(sK1(sK4,sK5,sK6),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_9961,c_59,c_62,c_4189]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.25/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1987,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.25/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_10238,plain,
% 23.25/3.49      ( r1_tarski(sK1(sK4,sK5,sK6),k2_struct_0(sK5)) = iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_10233,c_1987]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_18,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.25/3.49      | ~ v1_xboole_0(X2)
% 23.25/3.49      | v1_xboole_0(X0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f96]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1982,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.25/3.49      | v1_xboole_0(X2) != iProver_top
% 23.25/3.49      | v1_xboole_0(X0) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9258,plain,
% 23.25/3.49      ( v1_xboole_0(k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_4188,c_1982]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_52,negated_conjecture,
% 23.25/3.49      ( v1_tdlat_3(sK4) ),
% 23.25/3.49      inference(cnf_transformation,[],[f124]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_0,plain,
% 23.25/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_176,plain,
% 23.25/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_41,plain,
% 23.25/3.49      ( v3_pre_topc(X0,X1)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.25/3.49      | ~ v1_tdlat_3(X1)
% 23.25/3.49      | ~ v2_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X1) ),
% 23.25/3.49      inference(cnf_transformation,[],[f117]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2619,plain,
% 23.25/3.49      ( v3_pre_topc(X0,sK4)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.25/3.49      | ~ v1_tdlat_3(sK4)
% 23.25/3.49      | ~ v2_pre_topc(sK4)
% 23.25/3.49      | ~ l1_pre_topc(sK4) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_41]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2978,plain,
% 23.25/3.49      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0),sK4)
% 23.25/3.49      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.25/3.49      | ~ v1_tdlat_3(sK4)
% 23.25/3.49      | ~ v2_pre_topc(sK4)
% 23.25/3.49      | ~ l1_pre_topc(sK4) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_2619]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3539,plain,
% 23.25/3.49      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),sK4)
% 23.25/3.49      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.25/3.49      | ~ v1_tdlat_3(sK4)
% 23.25/3.49      | ~ v2_pre_topc(sK4)
% 23.25/3.49      | ~ l1_pre_topc(sK4) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_2978]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_28,plain,
% 23.25/3.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.25/3.49      | v5_pre_topc(X0,X1,X2)
% 23.25/3.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.25/3.49      | ~ v1_funct_1(X0)
% 23.25/3.49      | ~ l1_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X2)
% 23.25/3.49      | k2_struct_0(X2) = k1_xboole_0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f111]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3540,plain,
% 23.25/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
% 23.25/3.49      | v5_pre_topc(sK6,sK4,sK5)
% 23.25/3.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),sK4)
% 23.25/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 23.25/3.49      | ~ v1_funct_1(sK6)
% 23.25/3.49      | ~ l1_pre_topc(sK5)
% 23.25/3.49      | ~ l1_pre_topc(sK4)
% 23.25/3.49      | k2_struct_0(sK5) = k1_xboole_0 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_28]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_19,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.25/3.49      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 23.25/3.49      inference(cnf_transformation,[],[f97]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2632,plain,
% 23.25/3.49      ( m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.25/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_19]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_4591,plain,
% 23.25/3.49      ( m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK0(sK4,sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.25/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_2632]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_857,plain,
% 23.25/3.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3286,plain,
% 23.25/3.49      ( ~ v1_xboole_0(X0)
% 23.25/3.49      | v1_xboole_0(k2_struct_0(X1))
% 23.25/3.49      | k2_struct_0(X1) != X0 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_857]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_6744,plain,
% 23.25/3.49      ( v1_xboole_0(k2_struct_0(sK5))
% 23.25/3.49      | ~ v1_xboole_0(k1_xboole_0)
% 23.25/3.49      | k2_struct_0(sK5) != k1_xboole_0 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_3286]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_6745,plain,
% 23.25/3.49      ( k2_struct_0(sK5) != k1_xboole_0
% 23.25/3.49      | v1_xboole_0(k2_struct_0(sK5)) = iProver_top
% 23.25/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_6744]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9609,plain,
% 23.25/3.49      ( v1_xboole_0(sK6) = iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_9258,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_176,c_3539,
% 23.25/3.49                 c_3540,c_4591,c_6745]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1995,plain,
% 23.25/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_6,plain,
% 23.25/3.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 23.25/3.49      inference(cnf_transformation,[],[f84]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1990,plain,
% 23.25/3.49      ( X0 = X1
% 23.25/3.49      | v1_xboole_0(X0) != iProver_top
% 23.25/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_4388,plain,
% 23.25/3.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_1995,c_1990]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9615,plain,
% 23.25/3.49      ( sK6 = k1_xboole_0 ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_9609,c_4388]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_34,plain,
% 23.25/3.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.25/3.49      | ~ v5_pre_topc(X0,X1,X2)
% 23.25/3.49      | ~ v3_pre_topc(X3,X2)
% 23.25/3.49      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.25/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 23.25/3.49      | ~ v1_funct_1(X0)
% 23.25/3.49      | ~ l1_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X2)
% 23.25/3.49      | k2_struct_0(X2) = k1_xboole_0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f105]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1966,plain,
% 23.25/3.49      ( k2_struct_0(X0) = k1_xboole_0
% 23.25/3.49      | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X1,X2,X0) != iProver_top
% 23.25/3.49      | v3_pre_topc(X3,X0) != iProver_top
% 23.25/3.49      | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,X3),X2) = iProver_top
% 23.25/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 23.25/3.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.25/3.49      | v1_funct_1(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X2) != iProver_top
% 23.25/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_12336,plain,
% 23.25/3.49      ( k2_struct_0(sK5) = k1_xboole_0
% 23.25/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) != iProver_top
% 23.25/3.49      | v3_pre_topc(X2,sK5) != iProver_top
% 23.25/3.49      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,X2),X1) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_3646,c_1966]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_12347,plain,
% 23.25/3.49      ( k2_struct_0(sK5) = k1_xboole_0
% 23.25/3.49      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) != iProver_top
% 23.25/3.49      | v3_pre_topc(X2,sK5) != iProver_top
% 23.25/3.49      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,X2),X1) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_12336,c_3646]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13803,plain,
% 23.25/3.49      ( k2_struct_0(sK5) = k1_xboole_0 ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_12347,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_3539,
% 23.25/3.49                 c_3540,c_4591]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17457,plain,
% 23.25/3.49      ( r1_tarski(sK1(sK4,sK5,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_10238,c_9615,c_13803]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_5,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f83]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1991,plain,
% 23.25/3.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17461,plain,
% 23.25/3.49      ( sK1(sK4,sK5,k1_xboole_0) = k1_xboole_0 ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_17457,c_1991]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13835,plain,
% 23.25/3.49      ( u1_struct_0(sK5) = k1_xboole_0 ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_13803,c_3646]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_35,plain,
% 23.25/3.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.25/3.49      | v5_pre_topc(X0,X1,X2)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.25/3.49      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))))
% 23.25/3.49      | ~ v1_funct_1(X0)
% 23.25/3.49      | ~ v2_pre_topc(X1)
% 23.25/3.49      | ~ v2_pre_topc(X2)
% 23.25/3.49      | ~ l1_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X2) ),
% 23.25/3.49      inference(cnf_transformation,[],[f115]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1965,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,X2) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(X2) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X2) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14167,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_13835,c_1965]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14223,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_14167,c_13835]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_7,plain,
% 23.25/3.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f134]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14224,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_14223,c_7]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_873,plain,
% 23.25/3.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3467,plain,
% 23.25/3.49      ( ~ v1_funct_1(X0)
% 23.25/3.49      | v1_funct_1(X1)
% 23.25/3.49      | ~ v1_xboole_0(X1)
% 23.25/3.49      | ~ v1_xboole_0(X0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_6,c_873]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_5546,plain,
% 23.25/3.49      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK6) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_3467,c_48]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_5547,plain,
% 23.25/3.49      ( v1_funct_1(X0) = iProver_top
% 23.25/3.49      | v1_xboole_0(X0) != iProver_top
% 23.25/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_5546]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_5549,plain,
% 23.25/3.49      ( v1_funct_1(k1_xboole_0) = iProver_top
% 23.25/3.49      | v1_xboole_0(sK6) != iProver_top
% 23.25/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_5547]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_10846,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_3646,c_1965]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_10856,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK5) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK5) != iProver_top ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_10846,c_3646]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_11233,plain,
% 23.25/3.49      ( l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_10856,c_57,c_58]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_11234,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK5)))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK5),X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(renaming,[status(thm)],[c_11233]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13812,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_13803,c_11234]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14011,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_13812,c_7]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_858,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_8056,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,X1)
% 23.25/3.49      | r1_tarski(X2,X3)
% 23.25/3.49      | ~ v1_xboole_0(X1)
% 23.25/3.49      | ~ v1_xboole_0(X3)
% 23.25/3.49      | X2 != X0 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_858,c_6]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_30,plain,
% 23.25/3.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.25/3.49      | v5_pre_topc(X0,X1,X2)
% 23.25/3.49      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.25/3.49      | ~ v1_funct_1(X0)
% 23.25/3.49      | ~ l1_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X2)
% 23.25/3.49      | k2_struct_0(X2) = k1_xboole_0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f109]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_12973,plain,
% 23.25/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
% 23.25/3.49      | v5_pre_topc(sK6,sK4,sK5)
% 23.25/3.49      | v3_pre_topc(sK0(sK4,sK5,sK6),sK5)
% 23.25/3.49      | ~ v1_funct_1(sK6)
% 23.25/3.49      | ~ l1_pre_topc(sK5)
% 23.25/3.49      | ~ l1_pre_topc(sK4)
% 23.25/3.49      | k2_struct_0(sK5) = k1_xboole_0 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_30,c_46]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13658,plain,
% 23.25/3.49      ( k2_struct_0(sK5) = k1_xboole_0 ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_12973,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_3539,
% 23.25/3.49                 c_3540,c_4591]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_42981,plain,
% 23.25/3.49      ( r1_tarski(k2_struct_0(sK5),X0)
% 23.25/3.49      | ~ r1_tarski(k1_xboole_0,X1)
% 23.25/3.49      | ~ v1_xboole_0(X1)
% 23.25/3.49      | ~ v1_xboole_0(X0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_8056,c_13658]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_4,plain,
% 23.25/3.49      ( r1_tarski(k1_xboole_0,X0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f82]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_861,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_855,plain,( X0 = X0 ),theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_8120,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_861,c_855]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13682,plain,
% 23.25/3.49      ( m1_subset_1(k2_struct_0(sK5),X0) | ~ m1_subset_1(k1_xboole_0,X0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_13658,c_8120]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_16725,plain,
% 23.25/3.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 23.25/3.49      | r1_tarski(k2_struct_0(sK5),X0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_13682,c_13]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_12,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.25/3.49      inference(cnf_transformation,[],[f91]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_18667,plain,
% 23.25/3.49      ( r1_tarski(k2_struct_0(sK5),X0) | ~ r1_tarski(k1_xboole_0,X0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_16725,c_12]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_44158,plain,
% 23.25/3.49      ( r1_tarski(k2_struct_0(sK5),X0) ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_42981,c_4,c_18667]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_856,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.25/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_6860,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_856,c_1]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_6872,plain,
% 23.25/3.49      ( X0 != X1 | X1 = X0 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_856,c_855]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_19531,plain,
% 23.25/3.49      ( k1_xboole_0 = k2_struct_0(sK5) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_6872,c_13658]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_41001,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,k2_struct_0(sK5))
% 23.25/3.49      | ~ r1_tarski(k2_struct_0(sK5),X0)
% 23.25/3.49      | X0 = k1_xboole_0 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_6860,c_19531]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_44208,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,k2_struct_0(sK5)) | X0 = k1_xboole_0 ),
% 23.25/3.49      inference(backward_subsumption_resolution,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_44158,c_41001]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_45005,plain,
% 23.25/3.49      ( ~ r1_tarski(X0,k2_struct_0(sK5))
% 23.25/3.49      | v1_funct_1(X0)
% 23.25/3.49      | ~ v1_funct_1(k1_xboole_0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_44208,c_873]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_45027,plain,
% 23.25/3.49      ( r1_tarski(X0,k2_struct_0(sK5)) != iProver_top
% 23.25/3.49      | v1_funct_1(X0) = iProver_top
% 23.25/3.49      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_45005]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_860,plain,
% 23.25/3.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_8122,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.25/3.49      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 23.25/3.49      | X2 != X0
% 23.25/3.49      | X3 != X1 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_861,c_860]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_46685,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5)))
% 23.25/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
% 23.25/3.49      | X0 != X1 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_8122,c_13658]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_47396,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5)))
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_46685,c_855]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_50254,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 23.25/3.49      | r1_tarski(X0,k2_struct_0(sK5)) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_47396,c_13]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_50257,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | r1_tarski(X0,k2_struct_0(sK5)) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_50254]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_87392,plain,
% 23.25/3.49      ( l1_pre_topc(X1) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_14224,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_176,
% 23.25/3.49                 c_3539,c_3540,c_4591,c_5549,c_6745,c_9258,c_14011,c_45027,
% 23.25/3.49                 c_50257]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_87393,plain,
% 23.25/3.49      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(X0,X1,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK1(X1,sK5,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK5,sK1(X1,sK5,X0)))) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(renaming,[status(thm)],[c_87392]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_87410,plain,
% 23.25/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK4),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(k1_xboole_0,sK4,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK4) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_17461,c_87393]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_21,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.25/3.49      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f100]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1979,plain,
% 23.25/3.49      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 23.25/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_7585,plain,
% 23.25/3.49      ( k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6,k2_struct_0(sK5)) = k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_4188,c_1979]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_20,plain,
% 23.25/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.25/3.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f98]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1980,plain,
% 23.25/3.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.25/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_4601,plain,
% 23.25/3.49      ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k1_relat_1(sK6) ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_4188,c_1980]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_7597,plain,
% 23.25/3.49      ( k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6,k2_struct_0(sK5)) = k1_relat_1(sK6) ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_7585,c_4601]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17825,plain,
% 23.25/3.49      ( k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 23.25/3.49      inference(light_normalisation,[status(thm)],[c_7597,c_9615,c_13803]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1981,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.25/3.49      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17827,plain,
% 23.25/3.49      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top
% 23.25/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k1_xboole_0))) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_17825,c_1981]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17828,plain,
% 23.25/3.49      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top
% 23.25/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_17827,c_7]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_155,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.25/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_157,plain,
% 23.25/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 23.25/3.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_155]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_170,plain,
% 23.25/3.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_172,plain,
% 23.25/3.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_170]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_18196,plain,
% 23.25/3.49      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_17828,c_157,c_172]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_44,plain,
% 23.25/3.49      ( v4_pre_topc(X0,X1)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.25/3.49      | ~ v1_tdlat_3(X1)
% 23.25/3.49      | ~ v2_pre_topc(X1)
% 23.25/3.49      | ~ l1_pre_topc(X1) ),
% 23.25/3.49      inference(cnf_transformation,[],[f120]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1956,plain,
% 23.25/3.49      ( v4_pre_topc(X0,X1) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.25/3.49      | v1_tdlat_3(X1) != iProver_top
% 23.25/3.49      | v2_pre_topc(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_38,plain,
% 23.25/3.49      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f116]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1962,plain,
% 23.25/3.49      ( v1_tdlat_3(X0) != iProver_top
% 23.25/3.49      | v2_pre_topc(X0) = iProver_top
% 23.25/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2156,plain,
% 23.25/3.49      ( v4_pre_topc(X0,X1) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.25/3.49      | v1_tdlat_3(X1) != iProver_top
% 23.25/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.25/3.49      inference(forward_subsumption_resolution,[status(thm)],[c_1956,c_1962]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_27971,plain,
% 23.25/3.49      ( v4_pre_topc(X0,sK4) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 23.25/3.49      | v1_tdlat_3(sK4) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_3849,c_2156]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_55,plain,
% 23.25/3.49      ( v1_tdlat_3(sK4) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_29504,plain,
% 23.25/3.49      ( v4_pre_topc(X0,sK4) = iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_27971,c_55,c_56]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_29517,plain,
% 23.25/3.49      ( v4_pre_topc(k1_relat_1(k1_xboole_0),sK4) = iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_18196,c_29504]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_26,plain,
% 23.25/3.49      ( ~ v4_pre_topc(X0,X1)
% 23.25/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.25/3.49      | ~ l1_pre_topc(X1)
% 23.25/3.49      | k2_pre_topc(X1,X0) = X0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f103]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1974,plain,
% 23.25/3.49      ( k2_pre_topc(X0,X1) = X1
% 23.25/3.49      | v4_pre_topc(X1,X0) != iProver_top
% 23.25/3.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.25/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_12851,plain,
% 23.25/3.49      ( k2_pre_topc(sK4,X0) = X0
% 23.25/3.49      | v4_pre_topc(X0,sK4) != iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_3849,c_1974]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13136,plain,
% 23.25/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 23.25/3.49      | v4_pre_topc(X0,sK4) != iProver_top
% 23.25/3.49      | k2_pre_topc(sK4,X0) = X0 ),
% 23.25/3.49      inference(global_propositional_subsumption,[status(thm)],[c_12851,c_56]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13137,plain,
% 23.25/3.49      ( k2_pre_topc(sK4,X0) = X0
% 23.25/3.49      | v4_pre_topc(X0,sK4) != iProver_top
% 23.25/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 23.25/3.49      inference(renaming,[status(thm)],[c_13136]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_18202,plain,
% 23.25/3.49      ( k2_pre_topc(sK4,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
% 23.25/3.49      | v4_pre_topc(k1_relat_1(k1_xboole_0),sK4) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_18196,c_13137]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_29673,plain,
% 23.25/3.49      ( k2_pre_topc(sK4,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_29517,c_18202]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_87417,plain,
% 23.25/3.49      ( v1_funct_2(k1_xboole_0,k2_struct_0(sK4),k1_xboole_0) != iProver_top
% 23.25/3.49      | v5_pre_topc(k1_xboole_0,sK4,sK5) = iProver_top
% 23.25/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.25/3.49      | r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top
% 23.25/3.49      | v2_pre_topc(sK4) != iProver_top
% 23.25/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 23.25/3.49      inference(light_normalisation,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_87410,c_3849,c_17825,c_29673]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_13834,plain,
% 23.25/3.49      ( v1_funct_2(sK6,k2_struct_0(sK4),k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_13803,c_4189]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_16005,plain,
% 23.25/3.49      ( v1_funct_2(k1_xboole_0,k2_struct_0(sK4),k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_9615,c_13834]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1955,plain,
% 23.25/3.49      ( v5_pre_topc(sK6,sK4,sK5) != iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_16006,plain,
% 23.25/3.49      ( v5_pre_topc(k1_xboole_0,sK4,sK5) != iProver_top ),
% 23.25/3.49      inference(demodulation,[status(thm)],[c_9615,c_1955]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_87902,plain,
% 23.25/3.49      ( r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_87417,c_54,c_56,c_157,c_172,c_16005,c_16006]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_87907,plain,
% 23.25/3.49      ( v4_relat_1(k1_xboole_0,k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top
% 23.25/3.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_1985,c_87902]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_16,plain,
% 23.25/3.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.25/3.49      inference(cnf_transformation,[],[f94]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1984,plain,
% 23.25/3.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2987,plain,
% 23.25/3.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 23.25/3.49      inference(superposition,[status(thm)],[c_7,c_1984]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_88104,plain,
% 23.25/3.49      ( v4_relat_1(k1_xboole_0,k8_relset_1(k2_struct_0(sK4),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK5,k1_xboole_0))) != iProver_top ),
% 23.25/3.49      inference(global_propositional_subsumption,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_87907,c_2987]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17,plain,
% 23.25/3.49      ( v4_relat_1(k1_xboole_0,X0) ),
% 23.25/3.49      inference(cnf_transformation,[],[f95]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1983,plain,
% 23.25/3.49      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 23.25/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_88109,plain,
% 23.25/3.49      ( $false ),
% 23.25/3.49      inference(forward_subsumption_resolution,[status(thm)],[c_88104,c_1983]) ).
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.25/3.49  
% 23.25/3.49  ------                               Statistics
% 23.25/3.49  
% 23.25/3.49  ------ Selected
% 23.25/3.49  
% 23.25/3.49  total_time:                             2.705
% 23.25/3.49  
%------------------------------------------------------------------------------
