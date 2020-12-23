%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:08 EST 2020

% Result     : CounterSatisfiable 3.02s
% Output     : Saturation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  706 (18793 expanded)
%              Number of clauses        :  618 (4601 expanded)
%              Number of leaves         :   25 (5608 expanded)
%              Depth                    :   32
%              Number of atoms          : 3851 (112671 expanded)
%              Number of equality atoms : 1401 (7825 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4)
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2)
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f49,f48,f47])).

fof(f79,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f81,plain,(
    ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4840,plain,
    ( k5_tmap_1(X0_57,X0_56) = k5_tmap_1(X1_57,X1_56)
    | X0_57 != X1_57
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_4839,plain,
    ( u1_pre_topc(X0_57) = u1_pre_topc(X1_57)
    | X0_57 != X1_57 ),
    theory(equality)).

cnf(c_4821,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_4817,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_183,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_22])).

cnf(c_184,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1147,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_26])).

cnf(c_1148,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_1147])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1150,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1148,c_30,c_29,c_28,c_27])).

cnf(c_4805,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1150])).

cnf(c_23,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_911,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X0
    | X2 != X1
    | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1)) ),
    inference(resolution_lifted,[status(thm)],[c_184,c_23])).

cnf(c_912,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0)) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_2390,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_912,c_27])).

cnf(c_2391,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k5_tmap_1(sK3,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_2390])).

cnf(c_4793,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k5_tmap_1(sK3,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK3,sK3)) ),
    inference(subtyping,[status(esa)],[c_2391])).

cnf(c_2574,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_912,c_30])).

cnf(c_2575,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_2574])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_42,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_48,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2577,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2575,c_30,c_29,c_28,c_39,c_42,c_48])).

cnf(c_4785,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_2577])).

cnf(c_322,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1403,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_1404,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1403])).

cnf(c_1408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1404,c_30,c_29,c_28])).

cnf(c_1409,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1408])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_959,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X0
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_960,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_2555,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_960,c_30])).

cnf(c_2556,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2555])).

cnf(c_54,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2558,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2556,c_30,c_29,c_28,c_39,c_54])).

cnf(c_4053,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK2) != X0
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1409,c_2558])).

cnf(c_4054,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_4053])).

cnf(c_4751,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_4054])).

cnf(c_5965,plain,
    ( sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4751])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1168,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_1169,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1168])).

cnf(c_1171,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_30,c_29,c_28,c_27])).

cnf(c_4803,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1171])).

cnf(c_6224,plain,
    ( sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5965,c_4803])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_977,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X0
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_978,plain,
    ( m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_977])).

cnf(c_2544,plain,
    ( m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_978,c_30])).

cnf(c_2545,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2544])).

cnf(c_60,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2547,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2545,c_30,c_29,c_28,c_39,c_60])).

cnf(c_4787,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) ),
    inference(subtyping,[status(esa)],[c_2547])).

cnf(c_5935,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4787])).

cnf(c_941,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X0
    | X2 != X1
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_942,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_2566,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_942,c_30])).

cnf(c_2567,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2566])).

cnf(c_45,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2569,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2567,c_30,c_29,c_28,c_39,c_45])).

cnf(c_4786,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2569])).

cnf(c_6032,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5935,c_4786])).

cnf(c_17,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_787,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_788,plain,
    ( v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_2617,plain,
    ( v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_788,c_30])).

cnf(c_2618,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2617])).

cnf(c_57,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2620,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_30,c_29,c_28,c_39,c_57])).

cnf(c_4783,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) ),
    inference(subtyping,[status(esa)],[c_2620])).

cnf(c_5936,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4783])).

cnf(c_6022,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5936,c_4786])).

cnf(c_6229,plain,
    ( sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6224,c_6032,c_6022])).

cnf(c_12,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_203,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_17])).

cnf(c_760,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_23])).

cnf(c_761,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
    | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_2628,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
    | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_761,c_30])).

cnf(c_2629,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2628])).

cnf(c_72,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2631,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2629,c_30,c_29,c_28,c_39,c_42,c_54,c_57,c_60,c_72])).

cnf(c_9,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_866,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_867,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_866])).

cnf(c_871,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_867,c_30,c_29,c_28])).

cnf(c_872,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_871])).

cnf(c_3241,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK2) != X0
    | k9_tmap_1(sK2,sK3) = X0
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_2631,c_872])).

cnf(c_3242,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_3241])).

cnf(c_3244,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3242,c_30,c_29,c_28,c_39,c_54])).

cnf(c_3245,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(renaming,[status(thm)],[c_3244])).

cnf(c_4779,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_3245])).

cnf(c_5941,plain,
    ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4779])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_213,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_22,c_15,c_14,c_13])).

cnf(c_214,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_893,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | X1 != X0
    | X1 != X2
    | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_214,c_23])).

cnf(c_894,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_2582,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_894,c_30])).

cnf(c_2583,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_2582])).

cnf(c_63,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_66,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_69,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_84,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2585,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2583,c_30,c_29,c_28,c_39,c_42,c_63,c_66,c_69,c_84])).

cnf(c_4784,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_2585])).

cnf(c_6378,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5941,c_4784,c_4786,c_4803])).

cnf(c_6379,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6378])).

cnf(c_6385,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6379,c_6032,c_6022])).

cnf(c_929,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_23])).

cnf(c_930,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_4807,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_930])).

cnf(c_5919,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4807])).

cnf(c_6820,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4786,c_5919])).

cnf(c_33,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_40,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_7393,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6820,c_33,c_40,c_43])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2880,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_30])).

cnf(c_2881,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2880])).

cnf(c_2885,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2881,c_29,c_28])).

cnf(c_4780,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_2885])).

cnf(c_5940,plain,
    ( k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4780])).

cnf(c_7398,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_7393,c_5940])).

cnf(c_8588,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6385,c_7398])).

cnf(c_8592,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_6229,c_8588])).

cnf(c_1139,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_26])).

cnf(c_1140,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1139])).

cnf(c_1142,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1140,c_30,c_29,c_28])).

cnf(c_4806,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1142])).

cnf(c_8593,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_8592,c_4803,c_4806])).

cnf(c_8594,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_8593])).

cnf(c_8703,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_6229,c_8594])).

cnf(c_1155,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_1156,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1155])).

cnf(c_1158,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1156,c_28])).

cnf(c_4804,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1158])).

cnf(c_5920,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4804])).

cnf(c_7296,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_5920,c_5940])).

cnf(c_8704,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_8703,c_7296])).

cnf(c_8705,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_8704])).

cnf(c_2456,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
    | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_761,c_27])).

cnf(c_2457,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2456])).

cnf(c_2351,plain,
    ( m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_978,c_27])).

cnf(c_2352,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2351])).

cnf(c_2364,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_960,c_27])).

cnf(c_2365,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2364])).

cnf(c_2459,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2457,c_2352,c_2365])).

cnf(c_2460,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(renaming,[status(thm)],[c_2459])).

cnf(c_2471,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2460,c_930])).

cnf(c_805,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X0
    | k9_tmap_1(X0,X1) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_806,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_2590,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_806,c_30])).

cnf(c_2591,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2590])).

cnf(c_2595,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_29,c_28])).

cnf(c_2596,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2595])).

cnf(c_3404,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = X0
    | k9_tmap_1(sK3,sK3) != X0
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_2471,c_2596])).

cnf(c_3405,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_3404])).

cnf(c_3407,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3405,c_2365])).

cnf(c_3408,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_3407])).

cnf(c_4774,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3408])).

cnf(c_5946,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4774])).

cnf(c_6519,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5946,c_4786])).

cnf(c_10288,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8705,c_6519])).

cnf(c_1346,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X2
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_1347,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1346])).

cnf(c_2776,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1347,c_30])).

cnf(c_2777,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2776])).

cnf(c_2781,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2777,c_29,c_28])).

cnf(c_2782,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2781])).

cnf(c_4287,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0
    | k9_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2782,c_2365])).

cnf(c_4288,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_4287])).

cnf(c_4741,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4288])).

cnf(c_5975,plain,
    ( sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4741])).

cnf(c_6280,plain,
    ( sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5975,c_4786])).

cnf(c_10287,plain,
    ( sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8705,c_6280])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1316,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X2
    | k9_tmap_1(X1,X2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_1317,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1316])).

cnf(c_2803,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1317,c_30])).

cnf(c_2804,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2803])).

cnf(c_2808,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2804,c_29,c_28])).

cnf(c_2809,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2808])).

cnf(c_4265,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = X0
    | k9_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2809,c_2365])).

cnf(c_4266,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_4265])).

cnf(c_4742,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4266])).

cnf(c_5974,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_6330,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5974,c_4786])).

cnf(c_10286,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8705,c_6330])).

cnf(c_2,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3124,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | X5 != X0
    | k9_tmap_1(sK2,sK2) = X5
    | k7_tmap_1(sK2,sK1(sK2,sK2,X5)) != X0
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X5))) != X2
    | u1_struct_0(k8_tmap_1(sK2,sK2)) != X4
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_2596])).

cnf(c_3125,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k9_tmap_1(sK2,sK2) = X0
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_3124])).

cnf(c_4229,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = X0
    | k9_tmap_1(sK3,sK3) != X0
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3125,c_2365])).

cnf(c_4230,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_4229])).

cnf(c_4743,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4230])).

cnf(c_5973,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4743])).

cnf(c_6608,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5973,c_4786])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_378,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_2639,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_30])).

cnf(c_2640,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2639])).

cnf(c_105,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_108,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2642,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2640,c_30,c_28,c_105,c_108])).

cnf(c_4782,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_2642])).

cnf(c_5937,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4782])).

cnf(c_6619,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6608,c_5937])).

cnf(c_10278,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8705,c_6619])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1049,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | X3 != X0
    | X3 != X1
    | k8_tmap_1(X0,X1) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_1050,plain,
    ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(X0,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1049])).

cnf(c_2285,plain,
    ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(X0,X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1050,c_27])).

cnf(c_2286,plain,
    ( m1_subset_1(sK0(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_2285])).

cnf(c_1202,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_1203,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1202])).

cnf(c_1205,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_30,c_29,c_28])).

cnf(c_3715,plain,
    ( m1_subset_1(sK0(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2286,c_1205])).

cnf(c_3716,plain,
    ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3715])).

cnf(c_1213,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_1214,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1213])).

cnf(c_1224,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_1225,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1224])).

cnf(c_3718,plain,
    ( ~ v2_pre_topc(sK3)
    | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3716,c_30,c_29,c_28,c_1214,c_1225])).

cnf(c_3719,plain,
    ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_3718])).

cnf(c_4762,plain,
    ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_3719])).

cnf(c_5954,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4762])).

cnf(c_2758,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_2759,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_2758])).

cnf(c_4781,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0_56) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_2759])).

cnf(c_4812,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0_56) = k6_partfun1(u1_struct_0(sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4781])).

cnf(c_5939,plain,
    ( k7_tmap_1(sK3,X0_56) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4812])).

cnf(c_9539,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5954,c_5939])).

cnf(c_4813,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4781])).

cnf(c_4887,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4813])).

cnf(c_9871,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK3))
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9539,c_4887])).

cnf(c_9872,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9871])).

cnf(c_1235,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_1236,plain,
    ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1235])).

cnf(c_1240,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1236,c_30,c_29,c_28])).

cnf(c_1241,plain,
    ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1240])).

cnf(c_995,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X0
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_996,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_2338,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_996,c_27])).

cnf(c_2339,plain,
    ( v1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2338])).

cnf(c_3847,plain,
    ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) = X0
    | k8_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1241,c_2339])).

cnf(c_3848,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3847])).

cnf(c_1031,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X0,X2))
    | X1 != X0
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_1032,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X0)) ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_2312,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1032,c_27])).

cnf(c_2313,plain,
    ( ~ v2_pre_topc(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2312])).

cnf(c_1013,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X0
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_1014,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_2325,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1014,c_27])).

cnf(c_2326,plain,
    ( v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2325])).

cnf(c_3850,plain,
    ( ~ v2_pre_topc(sK3)
    | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3848,c_2313,c_2326])).

cnf(c_3851,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(renaming,[status(thm)],[c_3850])).

cnf(c_4756,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_3851])).

cnf(c_5960,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
    | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4756])).

cnf(c_9677,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5960,c_5940])).

cnf(c_2486,plain,
    ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(X0,X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1050,c_30])).

cnf(c_2487,plain,
    ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2486])).

cnf(c_2491,plain,
    ( ~ l1_pre_topc(X0)
    | m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2487,c_29,c_28])).

cnf(c_2492,plain,
    ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2491])).

cnf(c_3785,plain,
    ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) = X0
    | k8_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2492,c_2339])).

cnf(c_3786,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3785])).

cnf(c_3788,plain,
    ( ~ v2_pre_topc(sK3)
    | m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3786,c_2313,c_2326])).

cnf(c_3789,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(renaming,[status(thm)],[c_3788])).

cnf(c_4759,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_3789])).

cnf(c_5957,plain,
    ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
    | m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4759])).

cnf(c_9546,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5957,c_5940])).

cnf(c_2533,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_996,c_30])).

cnf(c_2534,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2533])).

cnf(c_2536,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2534,c_30,c_29,c_28,c_39,c_63])).

cnf(c_3583,plain,
    ( m1_subset_1(sK0(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2536,c_2286])).

cnf(c_3584,plain,
    ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3583])).

cnf(c_3586,plain,
    ( ~ v2_pre_topc(sK3)
    | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3584,c_30,c_29,c_28,c_39,c_66,c_69])).

cnf(c_3587,plain,
    ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(renaming,[status(thm)],[c_3586])).

cnf(c_4771,plain,
    ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_3587])).

cnf(c_5949,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4771])).

cnf(c_9163,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5949,c_5939])).

cnf(c_9201,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK3))
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9163,c_4887])).

cnf(c_9202,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9201])).

cnf(c_3701,plain,
    ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK2) = X0
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2492,c_1205])).

cnf(c_3702,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3701])).

cnf(c_1881,plain,
    ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(X0,X0) = X1
    | k8_tmap_1(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1050,c_1205])).

cnf(c_1882,plain,
    ( m1_subset_1(sK0(X0,X0,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1881])).

cnf(c_1886,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK0(X0,X0,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_30,c_29,c_28,c_1214,c_1225])).

cnf(c_1887,plain,
    ( m1_subset_1(sK0(X0,X0,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1886])).

cnf(c_1889,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_3704,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3702,c_30,c_29,c_28,c_1889])).

cnf(c_4763,plain,
    ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_3704])).

cnf(c_5953,plain,
    ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4763])).

cnf(c_9059,plain,
    ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_5953,c_5940])).

cnf(c_3625,plain,
    ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK2) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2536,c_1241])).

cnf(c_3626,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3625])).

cnf(c_1683,plain,
    ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(X1,X1) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1241,c_996])).

cnf(c_1684,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(X0,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,X0))
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_1683])).

cnf(c_1688,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(X0,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1684,c_1014,c_1032])).

cnf(c_1689,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(X0,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(renaming,[status(thm)],[c_1688])).

cnf(c_1691,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_3628,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_30,c_29,c_28,c_1691])).

cnf(c_4768,plain,
    ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_3628])).

cnf(c_5950,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2)
    | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4768])).

cnf(c_8986,plain,
    ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_5950,c_5940])).

cnf(c_3,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3157,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k9_tmap_1(sK2,sK2) != X0
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != X3
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) != X5
    | u1_struct_0(k8_tmap_1(sK2,sK2)) != X2
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_2631])).

cnf(c_3158,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3157])).

cnf(c_2039,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(k9_tmap_1(X6,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(k8_tmap_1(X6,X6)))))
    | ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(u1_struct_0(X6)))
    | ~ v2_pre_topc(X6)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k9_tmap_1(X6,X6))
    | v2_struct_0(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(X6)
    | X3 = X0
    | k9_tmap_1(X6,X6) != X0
    | k7_tmap_1(X6,u1_struct_0(X6)) != X3
    | u1_struct_0(X6) != X4
    | u1_struct_0(X6) != X1
    | u1_struct_0(k6_tmap_1(X6,u1_struct_0(X6))) != X5
    | u1_struct_0(k8_tmap_1(X6,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_761])).

cnf(c_2040,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
    | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ m1_subset_1(k7_tmap_1(X0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X0))
    | ~ v1_funct_1(k7_tmap_1(X0,u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ l1_pre_topc(X0)
    | k7_tmap_1(X0,u1_struct_0(X0)) = k9_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_2039])).

cnf(c_2044,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
    | ~ m1_subset_1(k7_tmap_1(X0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))))
    | ~ v1_funct_1(k7_tmap_1(X0,u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ l1_pre_topc(X0)
    | k7_tmap_1(X0,u1_struct_0(X0)) = k9_tmap_1(X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2040,c_788,c_930,c_960,c_978])).

cnf(c_2045,plain,
    ( ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
    | ~ m1_subset_1(k7_tmap_1(X0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ l1_pre_topc(X0)
    | k7_tmap_1(X0,u1_struct_0(X0)) = k9_tmap_1(X0,X0) ),
    inference(renaming,[status(thm)],[c_2044])).

cnf(c_2047,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_3160,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3158,c_30,c_29,c_28,c_2047])).

cnf(c_3161,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
    inference(renaming,[status(thm)],[c_3160])).

cnf(c_4461,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3) ),
    inference(resolution_lifted,[status(thm)],[c_3161,c_2365])).

cnf(c_4734,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4461])).

cnf(c_5982,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4734])).

cnf(c_6416,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5982,c_4784,c_4786])).

cnf(c_6424,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6416,c_5937])).

cnf(c_8850,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | k9_tmap_1(sK3,sK3) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6424,c_7398])).

cnf(c_1189,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_1190,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1189])).

cnf(c_1192,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1190,c_30,c_29,c_28])).

cnf(c_1176,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_1177,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1176])).

cnf(c_1179,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1177,c_30,c_29,c_28])).

cnf(c_835,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_26])).

cnf(c_836,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_838,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_30,c_29,c_28])).

cnf(c_839,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_838])).

cnf(c_1165,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1158,c_839])).

cnf(c_1186,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1179,c_1165])).

cnf(c_1199,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1192,c_1186])).

cnf(c_3183,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k9_tmap_1(sK2,sK3) != X0
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1199])).

cnf(c_3184,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3183])).

cnf(c_2078,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k9_tmap_1(sK2,sK3) != X0
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1199])).

cnf(c_2079,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_2078])).

cnf(c_855,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_856,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_2081,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_30,c_29,c_28,c_856,c_1177,c_1190])).

cnf(c_2082,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_2081])).

cnf(c_3186,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3184,c_30,c_29,c_28,c_856,c_1177,c_1190,c_2079])).

cnf(c_3187,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_3186])).

cnf(c_4392,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(resolution_lifted,[status(thm)],[c_2558,c_3187])).

cnf(c_4737,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4392])).

cnf(c_5979,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4737])).

cnf(c_6356,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5979,c_4803,c_4806])).

cnf(c_6362,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6356,c_5937])).

cnf(c_4816,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_4861,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_4816])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_22])).

cnf(c_191,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_396,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK2,sK3)
    | sK4 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_24])).

cnf(c_397,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_401,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_27,c_25])).

cnf(c_402,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_401])).

cnf(c_1450,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_402])).

cnf(c_1451,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1450])).

cnf(c_404,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_1453,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1451,c_30,c_29,c_28,c_26,c_404,c_1140])).

cnf(c_4798,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(subtyping,[status(esa)],[c_1453])).

cnf(c_4838,plain,
    ( k2_tmap_1(X0_57,X1_57,X0_56,X2_57) = k2_tmap_1(X3_57,X4_57,X1_56,X5_57)
    | X0_57 != X3_57
    | X1_57 != X4_57
    | X2_57 != X5_57
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_6879,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != sK2
    | sK3 != sK3
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4838])).

cnf(c_6919,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_4816])).

cnf(c_8788,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6362,c_4861,c_4806,c_4798,c_6879,c_6919])).

cnf(c_8792,plain,
    ( k9_tmap_1(sK2,sK2) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8788,c_7296])).

cnf(c_8857,plain,
    ( k9_tmap_1(sK3,sK3) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8850,c_8792])).

cnf(c_4440,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3) ),
    inference(resolution_lifted,[status(thm)],[c_3161,c_1179])).

cnf(c_4735,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4440])).

cnf(c_5981,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4735])).

cnf(c_6367,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5981,c_4784,c_4786])).

cnf(c_6373,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6367,c_5937])).

cnf(c_8798,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | k9_tmap_1(sK2,sK3) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6373,c_7398])).

cnf(c_8803,plain,
    ( k9_tmap_1(sK2,sK3) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8798,c_8792])).

cnf(c_6105,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(light_normalisation,[status(thm)],[c_4798,c_4806])).

cnf(c_8139,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(demodulation,[status(thm)],[c_7296,c_6105])).

cnf(c_2416,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_806,c_27])).

cnf(c_2417,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_2416])).

cnf(c_3306,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) != X0
    | k9_tmap_1(sK3,sK3) = X0
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_1199,c_2417])).

cnf(c_3307,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_3306])).

cnf(c_3309,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3307,c_30,c_29,c_28,c_1177])).

cnf(c_3310,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_3309])).

cnf(c_4777,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3310])).

cnf(c_5943,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4777])).

cnf(c_6481,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5943,c_4803,c_4806])).

cnf(c_8138,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7296,c_6481])).

cnf(c_7484,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5919,c_5939])).

cnf(c_3054,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | X5 != X0
    | k9_tmap_1(sK2,sK3) = X5
    | k7_tmap_1(sK2,sK1(sK2,sK3,X5)) != X0
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X5))) != X2
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X4
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_872])).

cnf(c_3055,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k9_tmap_1(sK2,sK3) = X0
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_3054])).

cnf(c_4313,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = X0
    | k9_tmap_1(sK3,sK3) != X0
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3055,c_2365])).

cnf(c_4314,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_4313])).

cnf(c_4740,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4314])).

cnf(c_5976,plain,
    ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4740])).

cnf(c_6629,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5976,c_4803])).

cnf(c_6640,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6629,c_5937])).

cnf(c_3367,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = X0
    | k9_tmap_1(sK3,sK3) != X0
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_872,c_2471])).

cnf(c_3368,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_3367])).

cnf(c_3370,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3368,c_2365])).

cnf(c_3371,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_3370])).

cnf(c_4775,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3371])).

cnf(c_5945,plain,
    ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4775])).

cnf(c_6500,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5945,c_4803])).

cnf(c_1376,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_1377,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1376])).

cnf(c_1381,plain,
    ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1377,c_30,c_29,c_28])).

cnf(c_1382,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1381])).

cnf(c_4369,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = X0
    | k9_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1382,c_2365])).

cnf(c_4370,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_4369])).

cnf(c_4738,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4370])).

cnf(c_5978,plain,
    ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4738])).

cnf(c_6343,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5978,c_4803])).

cnf(c_4347,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0
    | k9_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1409,c_2365])).

cnf(c_4348,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_4347])).

cnf(c_4739,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4348])).

cnf(c_5977,plain,
    ( sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4739])).

cnf(c_6293,plain,
    ( sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5977,c_4803])).

cnf(c_4802,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(subtyping,[status(esa)],[c_1192])).

cnf(c_5921,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4802])).

cnf(c_6029,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5921,c_4803])).

cnf(c_858,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_856,c_30,c_29,c_28])).

cnf(c_4808,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_858])).

cnf(c_5918,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4808])).

cnf(c_6015,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5918,c_4803])).

cnf(c_3209,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(sK3)
    | X3 = X0
    | k9_tmap_1(sK3,sK3) != X0
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != X3
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))) != X5
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != X2
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_2471])).

cnf(c_3210,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3209])).

cnf(c_2443,plain,
    ( v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_788,c_27])).

cnf(c_2444,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2443])).

cnf(c_3212,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_2352,c_2365,c_2444])).

cnf(c_3213,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
    inference(renaming,[status(thm)],[c_3212])).

cnf(c_4489,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
    inference(resolution_lifted,[status(thm)],[c_1179,c_3213])).

cnf(c_4733,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_4489])).

cnf(c_5983,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4733])).

cnf(c_2650,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1347,c_27])).

cnf(c_2651,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_2650])).

cnf(c_4201,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) != X0
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2651,c_1179])).

cnf(c_4202,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK3,sK3,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_4201])).

cnf(c_4744,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK3,sK3,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4202])).

cnf(c_5972,plain,
    ( sK1(sK3,sK3,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4744])).

cnf(c_2677,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1317,c_27])).

cnf(c_2678,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_2677])).

cnf(c_4179,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) != X0
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2678,c_1179])).

cnf(c_4180,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_4179])).

cnf(c_4745,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4180])).

cnf(c_5971,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4745])).

cnf(c_3085,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ l1_pre_topc(sK3)
    | X5 != X0
    | k9_tmap_1(sK3,sK3) = X5
    | k7_tmap_1(sK3,sK1(sK3,sK3,X5)) != X0
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X5))) != X2
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != X4
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_2417])).

cnf(c_3086,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = X0
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_3085])).

cnf(c_4113,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK2,sK3) != X0
    | k9_tmap_1(sK3,sK3) = X0
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3086,c_1179])).

cnf(c_4114,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_4113])).

cnf(c_4748,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4114])).

cnf(c_5968,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4748])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1262,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X1,X2,X0) = u1_struct_0(X2)
    | k8_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_1263,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1262])).

cnf(c_1267,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1263,c_30,c_29,c_28])).

cnf(c_1268,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1267])).

cnf(c_3827,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0
    | k8_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1268,c_2339])).

cnf(c_3828,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3827])).

cnf(c_3830,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3828,c_2313,c_2326])).

cnf(c_4757,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
    | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3830])).

cnf(c_5959,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
    | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4757])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1289,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
    | k8_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_1290,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1289])).

cnf(c_1294,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1290,c_30,c_29,c_28])).

cnf(c_1295,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1294])).

cnf(c_3807,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0
    | k8_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1295,c_2339])).

cnf(c_3808,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3807])).

cnf(c_3810,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3808,c_2313,c_2326])).

cnf(c_4758,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_3810])).

cnf(c_5958,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4758])).

cnf(c_1109,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X3
    | k6_tmap_1(X1,sK0(X1,X3,X0)) != X0
    | k8_tmap_1(X1,X3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_1110,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
    | k8_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_2830,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
    | k8_tmap_1(X1,X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1110,c_30])).

cnf(c_2831,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2830])).

cnf(c_2835,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2831,c_29,c_28])).

cnf(c_2836,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2835])).

cnf(c_3761,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
    | k8_tmap_1(sK2,sK2) = X0
    | k8_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2836,c_2339])).

cnf(c_3762,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3761])).

cnf(c_3764,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3762,c_2313,c_2326])).

cnf(c_4760,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_3764])).

cnf(c_5956,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4760])).

cnf(c_1079,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X3
    | sK0(X1,X3,X0) = u1_struct_0(X3)
    | k8_tmap_1(X1,X3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_1080,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X1,X0) = u1_struct_0(X1)
    | k8_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1079])).

cnf(c_2855,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X1,X0) = u1_struct_0(X1)
    | k8_tmap_1(X1,X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1080,c_30])).

cnf(c_2856,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2855])).

cnf(c_2860,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2856,c_29,c_28])).

cnf(c_2861,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2860])).

cnf(c_3741,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = X0
    | k8_tmap_1(sK3,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2861,c_2339])).

cnf(c_3742,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3741])).

cnf(c_3744,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3742,c_2313,c_2326])).

cnf(c_4761,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
    | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_3744])).

cnf(c_5955,plain,
    ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
    | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4761])).

cnf(c_2704,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
    | k8_tmap_1(X1,X1) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1110,c_27])).

cnf(c_2705,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,X0)) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_2704])).

cnf(c_3681,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2705,c_1205])).

cnf(c_3682,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3681])).

cnf(c_3684,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3682,c_30,c_29,c_28,c_1214,c_1225])).

cnf(c_4764,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_3684])).

cnf(c_5952,plain,
    ( k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4764])).

cnf(c_2731,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X1,X0) = u1_struct_0(X1)
    | k8_tmap_1(X1,X1) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1080,c_27])).

cnf(c_2732,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_2731])).

cnf(c_3661,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2732,c_1205])).

cnf(c_3662,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3661])).

cnf(c_3664,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3662,c_30,c_29,c_28,c_1214,c_1225])).

cnf(c_4765,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3664])).

cnf(c_5951,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4765])).

cnf(c_3561,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK2) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2536,c_2705])).

cnf(c_3562,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3561])).

cnf(c_3564,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_30,c_29,c_28,c_39,c_66,c_69])).

cnf(c_4772,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_3564])).

cnf(c_5948,plain,
    ( k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4772])).

cnf(c_3541,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK2) != X0
    | k8_tmap_1(sK3,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2536,c_2732])).

cnf(c_3542,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3541])).

cnf(c_3544,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3542,c_30,c_29,c_28,c_39,c_66,c_69])).

cnf(c_4773,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3544])).

cnf(c_5947,plain,
    ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
    | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4773])).

cnf(c_5938,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4813])).

cnf(c_2403,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_894,c_27])).

cnf(c_2404,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_2403])).

cnf(c_4792,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_2404])).

cnf(c_5930,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4792])).

cnf(c_5929,plain,
    ( k5_tmap_1(sK3,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK3,sK3))
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4793])).

cnf(c_2377,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_942,c_27])).

cnf(c_2378,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2377])).

cnf(c_4794,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_2378])).

cnf(c_5928,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4794])).

cnf(c_1430,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X0 != X1
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_402])).

cnf(c_1431,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1430])).

cnf(c_1433,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_27])).

cnf(c_4799,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1433])).

cnf(c_5924,plain,
    ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4799])).

cnf(c_3603,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK2) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2536,c_1295])).

cnf(c_3604,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3603])).

cnf(c_1629,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(X1,X1) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1295,c_996])).

cnf(c_1630,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,X0))
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(X0,X0))) != k8_tmap_1(X0,X0)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_1634,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(X0,X0))) != k8_tmap_1(X0,X0)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_1014,c_1032])).

cnf(c_1635,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(X0,X0))) != k8_tmap_1(X0,X0)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(renaming,[status(thm)],[c_1634])).

cnf(c_1637,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1635])).

cnf(c_3606,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3604,c_30,c_29,c_28,c_1637])).

cnf(c_4770,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_3606])).

cnf(c_3614,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK2) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2536,c_1268])).

cnf(c_3615,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_3614])).

cnf(c_1656,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(X1,X1) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1268,c_996])).

cnf(c_1657,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,X0))
    | sK0(sK2,sK3,k8_tmap_1(X0,X0)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_1656])).

cnf(c_1661,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK0(sK2,sK3,k8_tmap_1(X0,X0)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1657,c_1014,c_1032])).

cnf(c_1662,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK3,k8_tmap_1(X0,X0)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
    inference(renaming,[status(thm)],[c_1661])).

cnf(c_1664,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_3617,plain,
    ( sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3615,c_30,c_29,c_28,c_1664])).

cnf(c_4769,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2)
    | sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3617])).

cnf(c_3639,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = X0
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2861,c_1205])).

cnf(c_3640,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3639])).

cnf(c_1817,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X1,X0) = u1_struct_0(X1)
    | k8_tmap_1(X1,X1) = X0
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1080,c_1205])).

cnf(c_1818,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | sK0(X0,X0,k8_tmap_1(sK2,sK3)) = u1_struct_0(X0)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1817])).

cnf(c_1822,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK0(X0,X0,k8_tmap_1(sK2,sK3)) = u1_struct_0(X0)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1818,c_30,c_29,c_28,c_1214,c_1225])).

cnf(c_1823,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK0(X0,X0,k8_tmap_1(sK2,sK3)) = u1_struct_0(X0)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1822])).

cnf(c_1825,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_3642,plain,
    ( sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_30,c_29,c_28,c_1825])).

cnf(c_4767,plain,
    ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
    | sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_3642])).

cnf(c_3650,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
    | k8_tmap_1(sK2,sK2) = X0
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2836,c_1205])).

cnf(c_3651,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_3650])).

cnf(c_1790,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
    | k8_tmap_1(X1,X1) = X0
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1110,c_1205])).

cnf(c_1791,plain,
    ( ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k6_tmap_1(X0,sK0(X0,X0,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1790])).

cnf(c_1795,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k6_tmap_1(X0,sK0(X0,X0,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_30,c_29,c_28,c_1214,c_1225])).

cnf(c_1796,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,sK0(X0,X0,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1795])).

cnf(c_1798,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_3653,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3651,c_30,c_29,c_28,c_1798])).

cnf(c_4766,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_3653])).

cnf(c_2522,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1014,c_30])).

cnf(c_2523,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2522])).

cnf(c_2525,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2523,c_30,c_29,c_28,c_39,c_66])).

cnf(c_4788,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_2525])).

cnf(c_5934,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4788])).

cnf(c_2511,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1032,c_30])).

cnf(c_2512,plain,
    ( ~ v2_pre_topc(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2511])).

cnf(c_2514,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2512,c_30,c_29,c_28,c_39,c_69])).

cnf(c_4789,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_2514])).

cnf(c_5933,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4789])).

cnf(c_2476,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_27])).

cnf(c_2477,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2476])).

cnf(c_4790,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_2477])).

cnf(c_5932,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4790])).

cnf(c_4791,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_2444])).

cnf(c_5931,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4791])).

cnf(c_4795,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_2352])).

cnf(c_5927,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4795])).

cnf(c_4796,plain,
    ( v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_2326])).

cnf(c_5926,plain,
    ( v2_pre_topc(k8_tmap_1(sK3,sK3)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4796])).

cnf(c_4797,plain,
    ( ~ v2_pre_topc(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_2313])).

cnf(c_5925,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK3,sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4797])).

cnf(c_1227,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1225,c_30,c_29,c_28])).

cnf(c_4800,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1227])).

cnf(c_5923,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4800])).

cnf(c_1216,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1214,c_30,c_29,c_28])).

cnf(c_4801,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1216])).

cnf(c_5922,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4801])).

cnf(c_4811,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_5915,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4811])).

cnf(c_4810,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_5916,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4810])).

cnf(c_4809,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_5917,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4809])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.02/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/1.01  
% 3.02/1.01  ------  iProver source info
% 3.02/1.01  
% 3.02/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.02/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/1.01  git: non_committed_changes: false
% 3.02/1.01  git: last_make_outside_of_git: false
% 3.02/1.01  
% 3.02/1.01  ------ 
% 3.02/1.01  
% 3.02/1.01  ------ Input Options
% 3.02/1.01  
% 3.02/1.01  --out_options                           all
% 3.02/1.01  --tptp_safe_out                         true
% 3.02/1.01  --problem_path                          ""
% 3.02/1.01  --include_path                          ""
% 3.02/1.01  --clausifier                            res/vclausify_rel
% 3.02/1.01  --clausifier_options                    --mode clausify
% 3.02/1.01  --stdin                                 false
% 3.02/1.01  --stats_out                             all
% 3.02/1.01  
% 3.02/1.01  ------ General Options
% 3.02/1.01  
% 3.02/1.01  --fof                                   false
% 3.02/1.01  --time_out_real                         305.
% 3.02/1.01  --time_out_virtual                      -1.
% 3.02/1.01  --symbol_type_check                     false
% 3.02/1.01  --clausify_out                          false
% 3.02/1.01  --sig_cnt_out                           false
% 3.02/1.01  --trig_cnt_out                          false
% 3.02/1.01  --trig_cnt_out_tolerance                1.
% 3.02/1.01  --trig_cnt_out_sk_spl                   false
% 3.02/1.01  --abstr_cl_out                          false
% 3.02/1.01  
% 3.02/1.01  ------ Global Options
% 3.02/1.01  
% 3.02/1.01  --schedule                              default
% 3.02/1.01  --add_important_lit                     false
% 3.02/1.01  --prop_solver_per_cl                    1000
% 3.02/1.01  --min_unsat_core                        false
% 3.02/1.01  --soft_assumptions                      false
% 3.02/1.01  --soft_lemma_size                       3
% 3.02/1.01  --prop_impl_unit_size                   0
% 3.02/1.01  --prop_impl_unit                        []
% 3.02/1.01  --share_sel_clauses                     true
% 3.02/1.01  --reset_solvers                         false
% 3.02/1.01  --bc_imp_inh                            [conj_cone]
% 3.02/1.01  --conj_cone_tolerance                   3.
% 3.02/1.01  --extra_neg_conj                        none
% 3.02/1.01  --large_theory_mode                     true
% 3.02/1.01  --prolific_symb_bound                   200
% 3.02/1.01  --lt_threshold                          2000
% 3.02/1.01  --clause_weak_htbl                      true
% 3.02/1.01  --gc_record_bc_elim                     false
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing Options
% 3.02/1.01  
% 3.02/1.01  --preprocessing_flag                    true
% 3.02/1.01  --time_out_prep_mult                    0.1
% 3.02/1.01  --splitting_mode                        input
% 3.02/1.01  --splitting_grd                         true
% 3.02/1.01  --splitting_cvd                         false
% 3.02/1.01  --splitting_cvd_svl                     false
% 3.02/1.01  --splitting_nvd                         32
% 3.02/1.01  --sub_typing                            true
% 3.02/1.01  --prep_gs_sim                           true
% 3.02/1.01  --prep_unflatten                        true
% 3.02/1.01  --prep_res_sim                          true
% 3.02/1.01  --prep_upred                            true
% 3.02/1.01  --prep_sem_filter                       exhaustive
% 3.02/1.01  --prep_sem_filter_out                   false
% 3.02/1.01  --pred_elim                             true
% 3.02/1.01  --res_sim_input                         true
% 3.02/1.01  --eq_ax_congr_red                       true
% 3.02/1.01  --pure_diseq_elim                       true
% 3.02/1.01  --brand_transform                       false
% 3.02/1.01  --non_eq_to_eq                          false
% 3.02/1.01  --prep_def_merge                        true
% 3.02/1.01  --prep_def_merge_prop_impl              false
% 3.02/1.01  --prep_def_merge_mbd                    true
% 3.02/1.01  --prep_def_merge_tr_red                 false
% 3.02/1.01  --prep_def_merge_tr_cl                  false
% 3.02/1.01  --smt_preprocessing                     true
% 3.02/1.01  --smt_ac_axioms                         fast
% 3.02/1.01  --preprocessed_out                      false
% 3.02/1.01  --preprocessed_stats                    false
% 3.02/1.01  
% 3.02/1.01  ------ Abstraction refinement Options
% 3.02/1.01  
% 3.02/1.01  --abstr_ref                             []
% 3.02/1.01  --abstr_ref_prep                        false
% 3.02/1.01  --abstr_ref_until_sat                   false
% 3.02/1.01  --abstr_ref_sig_restrict                funpre
% 3.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.01  --abstr_ref_under                       []
% 3.02/1.01  
% 3.02/1.01  ------ SAT Options
% 3.02/1.01  
% 3.02/1.01  --sat_mode                              false
% 3.02/1.01  --sat_fm_restart_options                ""
% 3.02/1.01  --sat_gr_def                            false
% 3.02/1.01  --sat_epr_types                         true
% 3.02/1.01  --sat_non_cyclic_types                  false
% 3.02/1.01  --sat_finite_models                     false
% 3.02/1.01  --sat_fm_lemmas                         false
% 3.02/1.01  --sat_fm_prep                           false
% 3.02/1.01  --sat_fm_uc_incr                        true
% 3.02/1.01  --sat_out_model                         small
% 3.02/1.01  --sat_out_clauses                       false
% 3.02/1.01  
% 3.02/1.01  ------ QBF Options
% 3.02/1.01  
% 3.02/1.01  --qbf_mode                              false
% 3.02/1.01  --qbf_elim_univ                         false
% 3.02/1.01  --qbf_dom_inst                          none
% 3.02/1.01  --qbf_dom_pre_inst                      false
% 3.02/1.01  --qbf_sk_in                             false
% 3.02/1.01  --qbf_pred_elim                         true
% 3.02/1.01  --qbf_split                             512
% 3.02/1.01  
% 3.02/1.01  ------ BMC1 Options
% 3.02/1.01  
% 3.02/1.01  --bmc1_incremental                      false
% 3.02/1.01  --bmc1_axioms                           reachable_all
% 3.02/1.01  --bmc1_min_bound                        0
% 3.02/1.01  --bmc1_max_bound                        -1
% 3.02/1.01  --bmc1_max_bound_default                -1
% 3.02/1.01  --bmc1_symbol_reachability              true
% 3.02/1.01  --bmc1_property_lemmas                  false
% 3.02/1.01  --bmc1_k_induction                      false
% 3.02/1.01  --bmc1_non_equiv_states                 false
% 3.02/1.01  --bmc1_deadlock                         false
% 3.02/1.01  --bmc1_ucm                              false
% 3.02/1.01  --bmc1_add_unsat_core                   none
% 3.02/1.01  --bmc1_unsat_core_children              false
% 3.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.01  --bmc1_out_stat                         full
% 3.02/1.01  --bmc1_ground_init                      false
% 3.02/1.01  --bmc1_pre_inst_next_state              false
% 3.02/1.01  --bmc1_pre_inst_state                   false
% 3.02/1.01  --bmc1_pre_inst_reach_state             false
% 3.02/1.01  --bmc1_out_unsat_core                   false
% 3.02/1.01  --bmc1_aig_witness_out                  false
% 3.02/1.01  --bmc1_verbose                          false
% 3.02/1.01  --bmc1_dump_clauses_tptp                false
% 3.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.01  --bmc1_dump_file                        -
% 3.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.01  --bmc1_ucm_extend_mode                  1
% 3.02/1.01  --bmc1_ucm_init_mode                    2
% 3.02/1.01  --bmc1_ucm_cone_mode                    none
% 3.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.01  --bmc1_ucm_relax_model                  4
% 3.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.01  --bmc1_ucm_layered_model                none
% 3.02/1.01  --bmc1_ucm_max_lemma_size               10
% 3.02/1.01  
% 3.02/1.01  ------ AIG Options
% 3.02/1.01  
% 3.02/1.01  --aig_mode                              false
% 3.02/1.01  
% 3.02/1.01  ------ Instantiation Options
% 3.02/1.01  
% 3.02/1.01  --instantiation_flag                    true
% 3.02/1.01  --inst_sos_flag                         false
% 3.02/1.01  --inst_sos_phase                        true
% 3.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.01  --inst_lit_sel_side                     num_symb
% 3.02/1.01  --inst_solver_per_active                1400
% 3.02/1.01  --inst_solver_calls_frac                1.
% 3.02/1.01  --inst_passive_queue_type               priority_queues
% 3.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.01  --inst_passive_queues_freq              [25;2]
% 3.02/1.01  --inst_dismatching                      true
% 3.02/1.01  --inst_eager_unprocessed_to_passive     true
% 3.02/1.01  --inst_prop_sim_given                   true
% 3.02/1.01  --inst_prop_sim_new                     false
% 3.02/1.01  --inst_subs_new                         false
% 3.02/1.01  --inst_eq_res_simp                      false
% 3.02/1.01  --inst_subs_given                       false
% 3.02/1.01  --inst_orphan_elimination               true
% 3.02/1.01  --inst_learning_loop_flag               true
% 3.02/1.01  --inst_learning_start                   3000
% 3.02/1.01  --inst_learning_factor                  2
% 3.02/1.01  --inst_start_prop_sim_after_learn       3
% 3.02/1.01  --inst_sel_renew                        solver
% 3.02/1.01  --inst_lit_activity_flag                true
% 3.02/1.01  --inst_restr_to_given                   false
% 3.02/1.01  --inst_activity_threshold               500
% 3.02/1.01  --inst_out_proof                        true
% 3.02/1.01  
% 3.02/1.01  ------ Resolution Options
% 3.02/1.01  
% 3.02/1.01  --resolution_flag                       true
% 3.02/1.01  --res_lit_sel                           adaptive
% 3.02/1.01  --res_lit_sel_side                      none
% 3.02/1.01  --res_ordering                          kbo
% 3.02/1.01  --res_to_prop_solver                    active
% 3.02/1.01  --res_prop_simpl_new                    false
% 3.02/1.01  --res_prop_simpl_given                  true
% 3.02/1.01  --res_passive_queue_type                priority_queues
% 3.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.01  --res_passive_queues_freq               [15;5]
% 3.02/1.01  --res_forward_subs                      full
% 3.02/1.01  --res_backward_subs                     full
% 3.02/1.01  --res_forward_subs_resolution           true
% 3.02/1.01  --res_backward_subs_resolution          true
% 3.02/1.01  --res_orphan_elimination                true
% 3.02/1.01  --res_time_limit                        2.
% 3.02/1.01  --res_out_proof                         true
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Options
% 3.02/1.01  
% 3.02/1.01  --superposition_flag                    true
% 3.02/1.01  --sup_passive_queue_type                priority_queues
% 3.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.01  --demod_completeness_check              fast
% 3.02/1.01  --demod_use_ground                      true
% 3.02/1.01  --sup_to_prop_solver                    passive
% 3.02/1.01  --sup_prop_simpl_new                    true
% 3.02/1.01  --sup_prop_simpl_given                  true
% 3.02/1.01  --sup_fun_splitting                     false
% 3.02/1.01  --sup_smt_interval                      50000
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Simplification Setup
% 3.02/1.01  
% 3.02/1.01  --sup_indices_passive                   []
% 3.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_full_bw                           [BwDemod]
% 3.02/1.01  --sup_immed_triv                        [TrivRules]
% 3.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_immed_bw_main                     []
% 3.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  
% 3.02/1.01  ------ Combination Options
% 3.02/1.01  
% 3.02/1.01  --comb_res_mult                         3
% 3.02/1.01  --comb_sup_mult                         2
% 3.02/1.01  --comb_inst_mult                        10
% 3.02/1.01  
% 3.02/1.01  ------ Debug Options
% 3.02/1.01  
% 3.02/1.01  --dbg_backtrace                         false
% 3.02/1.01  --dbg_dump_prop_clauses                 false
% 3.02/1.01  --dbg_dump_prop_clauses_file            -
% 3.02/1.01  --dbg_out_stat                          false
% 3.02/1.01  ------ Parsing...
% 3.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/1.01  ------ Proving...
% 3.02/1.01  ------ Problem Properties 
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  clauses                                 81
% 3.02/1.01  conjectures                             3
% 3.02/1.01  EPR                                     3
% 3.02/1.01  Horn                                    45
% 3.02/1.01  unary                                   20
% 3.02/1.01  binary                                  9
% 3.02/1.01  lits                                    329
% 3.02/1.01  lits eq                                 114
% 3.02/1.01  fd_pure                                 0
% 3.02/1.01  fd_pseudo                               0
% 3.02/1.01  fd_cond                                 0
% 3.02/1.01  fd_pseudo_cond                          0
% 3.02/1.01  AC symbols                              0
% 3.02/1.01  
% 3.02/1.01  ------ Schedule dynamic 5 is on 
% 3.02/1.01  
% 3.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  ------ 
% 3.02/1.01  Current options:
% 3.02/1.01  ------ 
% 3.02/1.01  
% 3.02/1.01  ------ Input Options
% 3.02/1.01  
% 3.02/1.01  --out_options                           all
% 3.02/1.01  --tptp_safe_out                         true
% 3.02/1.01  --problem_path                          ""
% 3.02/1.01  --include_path                          ""
% 3.02/1.01  --clausifier                            res/vclausify_rel
% 3.02/1.01  --clausifier_options                    --mode clausify
% 3.02/1.01  --stdin                                 false
% 3.02/1.01  --stats_out                             all
% 3.02/1.01  
% 3.02/1.01  ------ General Options
% 3.02/1.01  
% 3.02/1.01  --fof                                   false
% 3.02/1.01  --time_out_real                         305.
% 3.02/1.01  --time_out_virtual                      -1.
% 3.02/1.01  --symbol_type_check                     false
% 3.02/1.01  --clausify_out                          false
% 3.02/1.01  --sig_cnt_out                           false
% 3.02/1.01  --trig_cnt_out                          false
% 3.02/1.01  --trig_cnt_out_tolerance                1.
% 3.02/1.01  --trig_cnt_out_sk_spl                   false
% 3.02/1.01  --abstr_cl_out                          false
% 3.02/1.01  
% 3.02/1.01  ------ Global Options
% 3.02/1.01  
% 3.02/1.01  --schedule                              default
% 3.02/1.01  --add_important_lit                     false
% 3.02/1.01  --prop_solver_per_cl                    1000
% 3.02/1.01  --min_unsat_core                        false
% 3.02/1.01  --soft_assumptions                      false
% 3.02/1.01  --soft_lemma_size                       3
% 3.02/1.01  --prop_impl_unit_size                   0
% 3.02/1.01  --prop_impl_unit                        []
% 3.02/1.01  --share_sel_clauses                     true
% 3.02/1.01  --reset_solvers                         false
% 3.02/1.01  --bc_imp_inh                            [conj_cone]
% 3.02/1.01  --conj_cone_tolerance                   3.
% 3.02/1.01  --extra_neg_conj                        none
% 3.02/1.01  --large_theory_mode                     true
% 3.02/1.01  --prolific_symb_bound                   200
% 3.02/1.01  --lt_threshold                          2000
% 3.02/1.01  --clause_weak_htbl                      true
% 3.02/1.01  --gc_record_bc_elim                     false
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing Options
% 3.02/1.01  
% 3.02/1.01  --preprocessing_flag                    true
% 3.02/1.01  --time_out_prep_mult                    0.1
% 3.02/1.01  --splitting_mode                        input
% 3.02/1.01  --splitting_grd                         true
% 3.02/1.01  --splitting_cvd                         false
% 3.02/1.01  --splitting_cvd_svl                     false
% 3.02/1.01  --splitting_nvd                         32
% 3.02/1.01  --sub_typing                            true
% 3.02/1.01  --prep_gs_sim                           true
% 3.02/1.01  --prep_unflatten                        true
% 3.02/1.01  --prep_res_sim                          true
% 3.02/1.01  --prep_upred                            true
% 3.02/1.01  --prep_sem_filter                       exhaustive
% 3.02/1.01  --prep_sem_filter_out                   false
% 3.02/1.01  --pred_elim                             true
% 3.02/1.01  --res_sim_input                         true
% 3.02/1.01  --eq_ax_congr_red                       true
% 3.02/1.01  --pure_diseq_elim                       true
% 3.02/1.01  --brand_transform                       false
% 3.02/1.01  --non_eq_to_eq                          false
% 3.02/1.01  --prep_def_merge                        true
% 3.02/1.01  --prep_def_merge_prop_impl              false
% 3.02/1.01  --prep_def_merge_mbd                    true
% 3.02/1.01  --prep_def_merge_tr_red                 false
% 3.02/1.01  --prep_def_merge_tr_cl                  false
% 3.02/1.01  --smt_preprocessing                     true
% 3.02/1.01  --smt_ac_axioms                         fast
% 3.02/1.01  --preprocessed_out                      false
% 3.02/1.01  --preprocessed_stats                    false
% 3.02/1.01  
% 3.02/1.01  ------ Abstraction refinement Options
% 3.02/1.01  
% 3.02/1.01  --abstr_ref                             []
% 3.02/1.01  --abstr_ref_prep                        false
% 3.02/1.01  --abstr_ref_until_sat                   false
% 3.02/1.01  --abstr_ref_sig_restrict                funpre
% 3.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.01  --abstr_ref_under                       []
% 3.02/1.01  
% 3.02/1.01  ------ SAT Options
% 3.02/1.01  
% 3.02/1.01  --sat_mode                              false
% 3.02/1.01  --sat_fm_restart_options                ""
% 3.02/1.01  --sat_gr_def                            false
% 3.02/1.01  --sat_epr_types                         true
% 3.02/1.01  --sat_non_cyclic_types                  false
% 3.02/1.01  --sat_finite_models                     false
% 3.02/1.01  --sat_fm_lemmas                         false
% 3.02/1.01  --sat_fm_prep                           false
% 3.02/1.01  --sat_fm_uc_incr                        true
% 3.02/1.01  --sat_out_model                         small
% 3.02/1.01  --sat_out_clauses                       false
% 3.02/1.01  
% 3.02/1.01  ------ QBF Options
% 3.02/1.01  
% 3.02/1.01  --qbf_mode                              false
% 3.02/1.01  --qbf_elim_univ                         false
% 3.02/1.01  --qbf_dom_inst                          none
% 3.02/1.01  --qbf_dom_pre_inst                      false
% 3.02/1.01  --qbf_sk_in                             false
% 3.02/1.01  --qbf_pred_elim                         true
% 3.02/1.01  --qbf_split                             512
% 3.02/1.01  
% 3.02/1.01  ------ BMC1 Options
% 3.02/1.01  
% 3.02/1.01  --bmc1_incremental                      false
% 3.02/1.01  --bmc1_axioms                           reachable_all
% 3.02/1.01  --bmc1_min_bound                        0
% 3.02/1.01  --bmc1_max_bound                        -1
% 3.02/1.01  --bmc1_max_bound_default                -1
% 3.02/1.01  --bmc1_symbol_reachability              true
% 3.02/1.01  --bmc1_property_lemmas                  false
% 3.02/1.01  --bmc1_k_induction                      false
% 3.02/1.01  --bmc1_non_equiv_states                 false
% 3.02/1.01  --bmc1_deadlock                         false
% 3.02/1.01  --bmc1_ucm                              false
% 3.02/1.01  --bmc1_add_unsat_core                   none
% 3.02/1.01  --bmc1_unsat_core_children              false
% 3.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.01  --bmc1_out_stat                         full
% 3.02/1.01  --bmc1_ground_init                      false
% 3.02/1.01  --bmc1_pre_inst_next_state              false
% 3.02/1.01  --bmc1_pre_inst_state                   false
% 3.02/1.01  --bmc1_pre_inst_reach_state             false
% 3.02/1.01  --bmc1_out_unsat_core                   false
% 3.02/1.01  --bmc1_aig_witness_out                  false
% 3.02/1.01  --bmc1_verbose                          false
% 3.02/1.01  --bmc1_dump_clauses_tptp                false
% 3.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.01  --bmc1_dump_file                        -
% 3.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.01  --bmc1_ucm_extend_mode                  1
% 3.02/1.01  --bmc1_ucm_init_mode                    2
% 3.02/1.01  --bmc1_ucm_cone_mode                    none
% 3.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.01  --bmc1_ucm_relax_model                  4
% 3.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.01  --bmc1_ucm_layered_model                none
% 3.02/1.01  --bmc1_ucm_max_lemma_size               10
% 3.02/1.01  
% 3.02/1.01  ------ AIG Options
% 3.02/1.01  
% 3.02/1.01  --aig_mode                              false
% 3.02/1.01  
% 3.02/1.01  ------ Instantiation Options
% 3.02/1.01  
% 3.02/1.01  --instantiation_flag                    true
% 3.02/1.01  --inst_sos_flag                         false
% 3.02/1.01  --inst_sos_phase                        true
% 3.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.01  --inst_lit_sel_side                     none
% 3.02/1.01  --inst_solver_per_active                1400
% 3.02/1.01  --inst_solver_calls_frac                1.
% 3.02/1.01  --inst_passive_queue_type               priority_queues
% 3.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.01  --inst_passive_queues_freq              [25;2]
% 3.02/1.01  --inst_dismatching                      true
% 3.02/1.01  --inst_eager_unprocessed_to_passive     true
% 3.02/1.01  --inst_prop_sim_given                   true
% 3.02/1.01  --inst_prop_sim_new                     false
% 3.02/1.01  --inst_subs_new                         false
% 3.02/1.01  --inst_eq_res_simp                      false
% 3.02/1.01  --inst_subs_given                       false
% 3.02/1.01  --inst_orphan_elimination               true
% 3.02/1.01  --inst_learning_loop_flag               true
% 3.02/1.01  --inst_learning_start                   3000
% 3.02/1.01  --inst_learning_factor                  2
% 3.02/1.01  --inst_start_prop_sim_after_learn       3
% 3.02/1.01  --inst_sel_renew                        solver
% 3.02/1.01  --inst_lit_activity_flag                true
% 3.02/1.01  --inst_restr_to_given                   false
% 3.02/1.01  --inst_activity_threshold               500
% 3.02/1.01  --inst_out_proof                        true
% 3.02/1.01  
% 3.02/1.01  ------ Resolution Options
% 3.02/1.01  
% 3.02/1.01  --resolution_flag                       false
% 3.02/1.01  --res_lit_sel                           adaptive
% 3.02/1.01  --res_lit_sel_side                      none
% 3.02/1.01  --res_ordering                          kbo
% 3.02/1.01  --res_to_prop_solver                    active
% 3.02/1.01  --res_prop_simpl_new                    false
% 3.02/1.01  --res_prop_simpl_given                  true
% 3.02/1.01  --res_passive_queue_type                priority_queues
% 3.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.01  --res_passive_queues_freq               [15;5]
% 3.02/1.01  --res_forward_subs                      full
% 3.02/1.01  --res_backward_subs                     full
% 3.02/1.01  --res_forward_subs_resolution           true
% 3.02/1.01  --res_backward_subs_resolution          true
% 3.02/1.01  --res_orphan_elimination                true
% 3.02/1.01  --res_time_limit                        2.
% 3.02/1.01  --res_out_proof                         true
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Options
% 3.02/1.01  
% 3.02/1.01  --superposition_flag                    true
% 3.02/1.01  --sup_passive_queue_type                priority_queues
% 3.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.01  --demod_completeness_check              fast
% 3.02/1.01  --demod_use_ground                      true
% 3.02/1.01  --sup_to_prop_solver                    passive
% 3.02/1.01  --sup_prop_simpl_new                    true
% 3.02/1.01  --sup_prop_simpl_given                  true
% 3.02/1.01  --sup_fun_splitting                     false
% 3.02/1.01  --sup_smt_interval                      50000
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Simplification Setup
% 3.02/1.01  
% 3.02/1.01  --sup_indices_passive                   []
% 3.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_full_bw                           [BwDemod]
% 3.02/1.01  --sup_immed_triv                        [TrivRules]
% 3.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_immed_bw_main                     []
% 3.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  
% 3.02/1.01  ------ Combination Options
% 3.02/1.01  
% 3.02/1.01  --comb_res_mult                         3
% 3.02/1.01  --comb_sup_mult                         2
% 3.02/1.01  --comb_inst_mult                        10
% 3.02/1.01  
% 3.02/1.01  ------ Debug Options
% 3.02/1.01  
% 3.02/1.01  --dbg_backtrace                         false
% 3.02/1.01  --dbg_dump_prop_clauses                 false
% 3.02/1.01  --dbg_dump_prop_clauses_file            -
% 3.02/1.01  --dbg_out_stat                          false
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  ------ Proving...
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  % SZS output start Saturation for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  fof(f10,axiom,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f32,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f10])).
% 3.02/1.01  
% 3.02/1.01  fof(f33,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f32])).
% 3.02/1.01  
% 3.02/1.01  fof(f72,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f33])).
% 3.02/1.01  
% 3.02/1.01  fof(f88,plain,(
% 3.02/1.01    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f72])).
% 3.02/1.01  
% 3.02/1.01  fof(f11,axiom,(
% 3.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f34,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f11])).
% 3.02/1.01  
% 3.02/1.01  fof(f73,plain,(
% 3.02/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f34])).
% 3.02/1.01  
% 3.02/1.01  fof(f13,conjecture,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f14,negated_conjecture,(
% 3.02/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 3.02/1.01    inference(negated_conjecture,[],[f13])).
% 3.02/1.01  
% 3.02/1.01  fof(f36,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f14])).
% 3.02/1.01  
% 3.02/1.01  fof(f37,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f49,plain,(
% 3.02/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f48,plain,(
% 3.02/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f47,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f50,plain,(
% 3.02/1.01    ((~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f49,f48,f47])).
% 3.02/1.01  
% 3.02/1.01  fof(f79,plain,(
% 3.02/1.01    m1_pre_topc(sK3,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f75,plain,(
% 3.02/1.01    ~v2_struct_0(sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f76,plain,(
% 3.02/1.01    v2_pre_topc(sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f77,plain,(
% 3.02/1.01    l1_pre_topc(sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f78,plain,(
% 3.02/1.01    ~v2_struct_0(sK3)),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f12,axiom,(
% 3.02/1.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f35,plain,(
% 3.02/1.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f12])).
% 3.02/1.01  
% 3.02/1.01  fof(f74,plain,(
% 3.02/1.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f35])).
% 3.02/1.01  
% 3.02/1.01  fof(f6,axiom,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f24,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f6])).
% 3.02/1.01  
% 3.02/1.01  fof(f25,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f24])).
% 3.02/1.01  
% 3.02/1.01  fof(f43,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(nnf_transformation,[],[f25])).
% 3.02/1.01  
% 3.02/1.01  fof(f44,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(rectify,[],[f43])).
% 3.02/1.01  
% 3.02/1.01  fof(f45,plain,(
% 3.02/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f46,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 3.02/1.01  
% 3.02/1.01  fof(f62,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f46])).
% 3.02/1.01  
% 3.02/1.01  fof(f8,axiom,(
% 3.02/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f28,plain,(
% 3.02/1.01    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f8])).
% 3.02/1.01  
% 3.02/1.01  fof(f29,plain,(
% 3.02/1.01    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f28])).
% 3.02/1.01  
% 3.02/1.01  fof(f67,plain,(
% 3.02/1.01    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f71,plain,(
% 3.02/1.01    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f33])).
% 3.02/1.01  
% 3.02/1.01  fof(f69,plain,(
% 3.02/1.01    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f68,plain,(
% 3.02/1.01    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f60,plain,(
% 3.02/1.01    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f46])).
% 3.02/1.01  
% 3.02/1.01  fof(f85,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f60])).
% 3.02/1.01  
% 3.02/1.01  fof(f86,plain,(
% 3.02/1.01    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f85])).
% 3.02/1.01  
% 3.02/1.01  fof(f63,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f46])).
% 3.02/1.01  
% 3.02/1.01  fof(f5,axiom,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f22,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f5])).
% 3.02/1.01  
% 3.02/1.01  fof(f23,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f22])).
% 3.02/1.01  
% 3.02/1.01  fof(f39,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(nnf_transformation,[],[f23])).
% 3.02/1.01  
% 3.02/1.01  fof(f40,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(rectify,[],[f39])).
% 3.02/1.01  
% 3.02/1.01  fof(f41,plain,(
% 3.02/1.01    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f42,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.02/1.01  
% 3.02/1.01  fof(f56,plain,(
% 3.02/1.01    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f83,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f56])).
% 3.02/1.01  
% 3.02/1.01  fof(f84,plain,(
% 3.02/1.01    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f83])).
% 3.02/1.01  
% 3.02/1.01  fof(f7,axiom,(
% 3.02/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f26,plain,(
% 3.02/1.01    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f7])).
% 3.02/1.01  
% 3.02/1.01  fof(f27,plain,(
% 3.02/1.01    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f26])).
% 3.02/1.01  
% 3.02/1.01  fof(f64,plain,(
% 3.02/1.01    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f27])).
% 3.02/1.01  
% 3.02/1.01  fof(f65,plain,(
% 3.02/1.01    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f27])).
% 3.02/1.01  
% 3.02/1.01  fof(f66,plain,(
% 3.02/1.01    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f27])).
% 3.02/1.01  
% 3.02/1.01  fof(f4,axiom,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f20,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f4])).
% 3.02/1.01  
% 3.02/1.01  fof(f21,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f20])).
% 3.02/1.01  
% 3.02/1.01  fof(f55,plain,(
% 3.02/1.01    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f21])).
% 3.02/1.01  
% 3.02/1.01  fof(f61,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f46])).
% 3.02/1.01  
% 3.02/1.01  fof(f3,axiom,(
% 3.02/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f18,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.02/1.01    inference(ennf_transformation,[],[f3])).
% 3.02/1.01  
% 3.02/1.01  fof(f19,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.02/1.01    inference(flattening,[],[f18])).
% 3.02/1.01  
% 3.02/1.01  fof(f38,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.02/1.01    inference(nnf_transformation,[],[f19])).
% 3.02/1.01  
% 3.02/1.01  fof(f54,plain,(
% 3.02/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f38])).
% 3.02/1.01  
% 3.02/1.01  fof(f82,plain,(
% 3.02/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.02/1.01    inference(equality_resolution,[],[f54])).
% 3.02/1.01  
% 3.02/1.01  fof(f1,axiom,(
% 3.02/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f15,plain,(
% 3.02/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f1])).
% 3.02/1.01  
% 3.02/1.01  fof(f51,plain,(
% 3.02/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f15])).
% 3.02/1.01  
% 3.02/1.01  fof(f2,axiom,(
% 3.02/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f16,plain,(
% 3.02/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f2])).
% 3.02/1.01  
% 3.02/1.01  fof(f17,plain,(
% 3.02/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f16])).
% 3.02/1.01  
% 3.02/1.01  fof(f52,plain,(
% 3.02/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f17])).
% 3.02/1.01  
% 3.02/1.01  fof(f57,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f53,plain,(
% 3.02/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f38])).
% 3.02/1.01  
% 3.02/1.01  fof(f9,axiom,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f30,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f9])).
% 3.02/1.01  
% 3.02/1.01  fof(f31,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f30])).
% 3.02/1.01  
% 3.02/1.01  fof(f70,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f87,plain,(
% 3.02/1.01    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f70])).
% 3.02/1.01  
% 3.02/1.01  fof(f81,plain,(
% 3.02/1.01    ~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f80,plain,(
% 3.02/1.01    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.02/1.01    inference(cnf_transformation,[],[f50])).
% 3.02/1.01  
% 3.02/1.01  fof(f58,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK0(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f59,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f42])).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4840,plain,
% 3.02/1.01      ( k5_tmap_1(X0_57,X0_56) = k5_tmap_1(X1_57,X1_56)
% 3.02/1.01      | X0_57 != X1_57
% 3.02/1.01      | X0_56 != X1_56 ),
% 3.02/1.01      theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4839,plain,
% 3.02/1.01      ( u1_pre_topc(X0_57) = u1_pre_topc(X1_57) | X0_57 != X1_57 ),
% 3.02/1.01      theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4821,plain,
% 3.02/1.01      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 3.02/1.01      theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4817,plain,( X0_58 = X0_58 ),theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_20,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_22,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_183,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.02/1.01      inference(global_propositional_subsumption,[status(thm)],[c_20,c_22]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_184,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_183]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_26,negated_conjecture,
% 3.02/1.01      ( m1_pre_topc(sK3,sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1147,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
% 3.02/1.01      | sK2 != X0
% 3.02/1.01      | sK3 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_184,c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1148,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | v2_struct_0(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1147]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_30,negated_conjecture,
% 3.02/1.01      ( ~ v2_struct_0(sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_29,negated_conjecture,
% 3.02/1.01      ( v2_pre_topc(sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_28,negated_conjecture,
% 3.02/1.01      ( l1_pre_topc(sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_27,negated_conjecture,
% 3.02/1.01      ( ~ v2_struct_0(sK3) ),
% 3.02/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1150,plain,
% 3.02/1.01      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1148,c_30,c_29,c_28,c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4805,plain,
% 3.02/1.01      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_1150]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_23,plain,
% 3.02/1.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_911,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X0
% 3.02/1.01      | X2 != X1
% 3.02/1.01      | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1)) ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_184,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_912,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0)) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_911]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2390,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.01      | sK3 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_912,c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2391,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k5_tmap_1(sK3,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK3,sK3)) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2390]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4793,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k5_tmap_1(sK3,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK3,sK3)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2391]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2574,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_912,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2575,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2574]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_39,plain,
% 3.02/1.01      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_42,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_48,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2577,plain,
% 3.02/1.01      ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2575,c_30,c_29,c_28,c_39,c_42,c_48]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4785,plain,
% 3.02/1.01      ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2577]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_322,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 3.02/1.01      | k9_tmap_1(X1,X2) = X0 ),
% 3.02/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1403,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 3.02/1.01      | k9_tmap_1(X1,X2) = X0
% 3.02/1.01      | sK2 != X1
% 3.02/1.01      | sK3 != X2 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1404,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1403]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1408,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1404,c_30,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1409,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_1408]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_18,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_959,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X0
% 3.02/1.01      | X2 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_960,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_959]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2555,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_960,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2556,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2555]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_54,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2558,plain,
% 3.02/1.01      ( v1_funct_1(k9_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2556,c_30,c_29,c_28,c_39,c_54]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4053,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) != X0
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_1409,c_2558]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4054,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_4053]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4751,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_4054]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5965,plain,
% 3.02/1.01      ( sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4751]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_21,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1168,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 3.02/1.01      | sK2 != X0
% 3.02/1.01      | sK3 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1169,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | v2_struct_0(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1168]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1171,plain,
% 3.02/1.01      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1169,c_30,c_29,c_28,c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4803,plain,
% 3.02/1.01      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_1171]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6224,plain,
% 3.02/1.01      ( sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_5965,c_4803]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_16,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_977,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X0
% 3.02/1.01      | X2 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_978,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_977]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2544,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_978,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2545,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2544]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_60,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2547,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2545,c_30,c_29,c_28,c_39,c_60]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4787,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2547]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5935,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4787]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_941,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X0
% 3.02/1.01      | X2 != X1
% 3.02/1.01      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0) ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_942,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_941]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2566,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0)
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_942,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2567,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2566]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_45,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2569,plain,
% 3.02/1.01      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2567,c_30,c_29,c_28,c_39,c_45]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4786,plain,
% 3.02/1.01      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2569]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6032,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_5935,c_4786]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_17,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.01      | ~ m1_pre_topc(X1,X0)
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_787,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X1
% 3.02/1.01      | X2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_788,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_787]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2617,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_788,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2618,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2617]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_57,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2620,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2618,c_30,c_29,c_28,c_39,c_57]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4783,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2620]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5936,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4783]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6022,plain,
% 3.02/1.01      ( v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_5936,c_4786]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6229,plain,
% 3.02/1.01      ( sK1(sK2,sK3,k9_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.01      inference(forward_subsumption_resolution,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_6224,c_6032,c_6022]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_12,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.02/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.01      | ~ m1_pre_topc(X1,X0)
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_203,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.02/1.01      | ~ m1_pre_topc(X1,X0)
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(global_propositional_subsumption,[status(thm)],[c_12,c_17]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_760,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X1
% 3.02/1.01      | X2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_203,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_761,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_760]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2628,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_761,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2629,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2628]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_72,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2631,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2))) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2629,c_30,c_29,c_28,c_39,c_42,c_54,c_57,c_60,c_72]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 3.02/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.01      | ~ m1_pre_topc(X1,X0)
% 3.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(X2)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k9_tmap_1(X0,X1) = X2 ),
% 3.02/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_866,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 3.02/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(X2)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k9_tmap_1(X0,X1) = X2
% 3.02/1.01      | sK2 != X0
% 3.02/1.01      | sK3 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_867,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_866]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_871,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_867,c_30,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_872,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_871]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3241,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) != X0
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = X0
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_2631,c_872]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3242,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_3241]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3244,plain,
% 3.02/1.01      ( ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_3242,c_30,c_29,c_28,c_39,c_54]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3245,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_3244]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4779,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_3245]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5941,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4779]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.02/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_15,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | v1_pre_topc(k8_tmap_1(X1,X0))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_14,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_pre_topc(k8_tmap_1(X1,X0))
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_13,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_213,plain,
% 3.02/1.01      ( ~ l1_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_8,c_22,c_15,c_14,c_13]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_214,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_213]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_893,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | X1 != X0
% 3.02/1.01      | X1 != X2
% 3.02/1.01      | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2) ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_214,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_894,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_893]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2582,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_894,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2583,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2582]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_63,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | v1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_66,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_69,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_84,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK2,sK2)
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2585,plain,
% 3.02/1.01      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2583,c_30,c_29,c_28,c_39,c_42,c_63,c_66,c_69,c_84]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4784,plain,
% 3.02/1.01      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2585]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6378,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.01      inference(light_normalisation,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5941,c_4784,c_4786,c_4803]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6379,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.01      inference(equality_resolution_simp,[status(thm)],[c_6378]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6385,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2) ),
% 3.02/1.01      inference(forward_subsumption_resolution,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_6379,c_6032,c_6022]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_929,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | ~ l1_pre_topc(X2)
% 3.02/1.01      | X2 != X1
% 3.02/1.01      | X2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_930,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ l1_pre_topc(X0) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_929]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4807,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 3.02/1.01      | ~ l1_pre_topc(X0_57) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_930]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5919,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
% 3.02/1.01      | l1_pre_topc(X0_57) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4807]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6820,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.01      | l1_pre_topc(k8_tmap_1(sK2,sK2)) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_4786,c_5919]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_33,plain,
% 3.02/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_38,plain,
% 3.02/1.01      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_40,plain,
% 3.02/1.01      ( m1_pre_topc(sK2,sK2) = iProver_top | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_38]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_41,plain,
% 3.02/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.02/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.02/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_43,plain,
% 3.02/1.01      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.02/1.01      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_41]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_7393,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_6820,c_33,c_40,c_43]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2880,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 3.02/1.01      | sK2 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2881,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2880]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2885,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2881,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4780,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2885]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5940,plain,
% 3.02/1.01      ( k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2))
% 3.02/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4780]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_7398,plain,
% 3.02/1.01      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_7393,c_5940]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8588,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2) ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_6385,c_7398]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8592,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != u1_struct_0(sK2) ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_6229,c_8588]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1139,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 3.02/1.01      | sK2 != X0
% 3.02/1.01      | sK3 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_214,c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1140,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK2)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1139]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1142,plain,
% 3.02/1.01      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1140,c_30,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4806,plain,
% 3.02/1.01      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_1142]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8593,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_8592,c_4803,c_4806]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8594,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(equality_resolution_simp,[status(thm)],[c_8593]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8703,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_6229,c_8594]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1155,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | sK2 != X1
% 3.02/1.01      | sK3 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1156,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1155]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1158,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.02/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1156,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4804,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_1158]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5920,plain,
% 3.02/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4804]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_7296,plain,
% 3.02/1.01      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5920,c_5940]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8704,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_8703,c_7296]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8705,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.01      inference(equality_resolution_simp,[status(thm)],[c_8704]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2456,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK3 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_761,c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2457,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
% 3.02/1.01      | ~ l1_pre_topc(sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2456]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2351,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK3 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_978,c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2352,plain,
% 3.02/1.01      ( m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2351]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2364,plain,
% 3.02/1.01      ( ~ v2_pre_topc(X0)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | sK3 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_960,c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2365,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK3)
% 3.02/1.01      | v1_funct_1(k9_tmap_1(sK3,sK3))
% 3.02/1.01      | ~ l1_pre_topc(sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2364]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2459,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.01      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | ~ l1_pre_topc(sK3) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2457,c_2352,c_2365]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2460,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_2459]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2471,plain,
% 3.02/1.01      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))),k9_tmap_1(sK3,sK3),k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3) ),
% 3.02/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2460,c_930]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_805,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 3.02/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(X2)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | ~ l1_pre_topc(X3)
% 3.02/1.01      | X3 != X1
% 3.02/1.01      | X3 != X0
% 3.02/1.01      | k9_tmap_1(X0,X1) = X2 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_806,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 3.02/1.01      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k9_tmap_1(X0,X0) = X1 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_805]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2590,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 3.02/1.01      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.01      | ~ v2_pre_topc(X0)
% 3.02/1.01      | ~ v1_funct_1(X1)
% 3.02/1.01      | ~ l1_pre_topc(X0)
% 3.02/1.01      | k9_tmap_1(X0,X0) = X1
% 3.02/1.01      | sK2 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_806,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2591,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2590]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2595,plain,
% 3.02/1.01      ( ~ v1_funct_1(X0)
% 3.02/1.01      | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2591,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2596,plain,
% 3.02/1.01      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_2595]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3404,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0
% 3.02/1.01      | k9_tmap_1(sK3,sK3) != X0
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_2471,c_2596]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3405,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_3404]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3407,plain,
% 3.02/1.01      ( ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3405,c_2365]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3408,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_3407]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4774,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_3408]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5946,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4774]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6519,plain,
% 3.02/1.01      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_5946,c_4786]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10288,plain,
% 3.02/1.01      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
% 3.02/1.01      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_8705,c_6519]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1346,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | ~ l1_pre_topc(X3)
% 3.02/1.01      | X3 != X1
% 3.02/1.01      | X3 != X2
% 3.02/1.01      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 3.02/1.01      | k9_tmap_1(X1,X2) = X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1347,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.01      | k9_tmap_1(X1,X1) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1346]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2776,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.01      | k9_tmap_1(X1,X1) = X0
% 3.02/1.01      | sK2 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_1347,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2777,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2776]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2781,plain,
% 3.02/1.01      ( ~ v1_funct_1(X0)
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2777,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2782,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_2781]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4287,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0
% 3.02/1.01      | k9_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_2782,c_2365]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4288,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_4287]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4741,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_4288]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5975,plain,
% 3.02/1.01      ( sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4741]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6280,plain,
% 3.02/1.01      ( sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_5975,c_4786]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10287,plain,
% 3.02/1.01      ( sK1(sK2,sK2,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.01      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_8705,c_6280]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_11,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.02/1.01      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k9_tmap_1(X1,X2) = X0 ),
% 3.02/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1316,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.02/1.01      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | ~ l1_pre_topc(X3)
% 3.02/1.01      | X3 != X1
% 3.02/1.01      | X3 != X2
% 3.02/1.01      | k9_tmap_1(X1,X2) = X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1317,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.02/1.01      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k9_tmap_1(X1,X1) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_1316]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2803,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.02/1.01      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.01      | ~ v2_pre_topc(X1)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | k9_tmap_1(X1,X1) = X0
% 3.02/1.01      | sK2 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_1317,c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2804,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK2)
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ l1_pre_topc(sK2)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_2803]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2808,plain,
% 3.02/1.01      ( ~ v1_funct_1(X0)
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2804,c_29,c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2809,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_2808]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4265,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X0
% 3.02/1.01      | k9_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_2809,c_2365]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4266,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_4265]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4742,plain,
% 3.02/1.01      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.01      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v2_pre_topc(sK3)
% 3.02/1.01      | ~ l1_pre_topc(sK3)
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_4266]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5974,plain,
% 3.02/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6330,plain,
% 3.02/1.01      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_5974,c_4786]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10286,plain,
% 3.02/1.01      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.01      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.01      | m1_subset_1(sK1(sK2,sK2,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.01      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_8705,c_6330]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2,plain,
% 3.02/1.01      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.02/1.01      | ~ v1_funct_2(X4,X2,X3)
% 3.02/1.01      | ~ v1_funct_2(X4,X0,X1)
% 3.02/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.02/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/1.01      | ~ v1_funct_1(X4)
% 3.02/1.01      | v1_xboole_0(X1)
% 3.02/1.01      | v1_xboole_0(X3) ),
% 3.02/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3124,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.01      | ~ v1_funct_2(X0,X3,X4)
% 3.02/1.01      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.02/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.01      | ~ v1_funct_1(X0)
% 3.02/1.01      | ~ v1_funct_1(X5)
% 3.02/1.01      | v1_xboole_0(X4)
% 3.02/1.01      | v1_xboole_0(X2)
% 3.02/1.01      | X5 != X0
% 3.02/1.01      | k9_tmap_1(sK2,sK2) = X5
% 3.02/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,X5)) != X0
% 3.02/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X5))) != X2
% 3.02/1.01      | u1_struct_0(k8_tmap_1(sK2,sK2)) != X4
% 3.02/1.01      | u1_struct_0(sK2) != X1
% 3.02/1.01      | u1_struct_0(sK2) != X3 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_2596]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3125,plain,
% 3.02/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
% 3.02/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | k9_tmap_1(sK2,sK2) = X0
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3124]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4229,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK2) = X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != X0
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3125,c_2365]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4230,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4229]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4743,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4230]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5973,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4743]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6608,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5973,c_4786]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_0,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.02/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1,plain,
% 3.02/1.02      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 3.02/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_378,plain,
% 3.02/1.02      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 3.02/1.02      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2639,plain,
% 3.02/1.02      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK2 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_378,c_30]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2640,plain,
% 3.02/1.02      ( ~ v1_xboole_0(u1_struct_0(sK2)) | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2639]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_105,plain,
% 3.02/1.02      ( v2_struct_0(sK2)
% 3.02/1.02      | ~ v1_xboole_0(u1_struct_0(sK2))
% 3.02/1.02      | ~ l1_struct_0(sK2) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_108,plain,
% 3.02/1.02      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2642,plain,
% 3.02/1.02      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2640,c_30,c_28,c_105,c_108]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4782,plain,
% 3.02/1.02      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_2642]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5937,plain,
% 3.02/1.02      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4782]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6619,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_6608,c_5937]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_10278,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(demodulation,[status(thm)],[c_8705,c_6619]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_7,plain,
% 3.02/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.02      | ~ v1_pre_topc(X2)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X2)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | k8_tmap_1(X1,X0) = X2 ),
% 3.02/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1049,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v1_pre_topc(X2)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X2)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | ~ l1_pre_topc(X3)
% 3.02/1.02      | X3 != X0
% 3.02/1.02      | X3 != X1
% 3.02/1.02      | k8_tmap_1(X0,X1) = X2 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1050,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v1_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k8_tmap_1(X0,X0) = X1 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1049]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2285,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v1_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k8_tmap_1(X0,X0) = X1
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1050,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2286,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2285]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1202,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(X0,X1))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1203,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1202]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1205,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1203,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3715,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2286,c_1205]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3716,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3715]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1213,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_pre_topc(k8_tmap_1(X0,X1))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1214,plain,
% 3.02/1.02      ( v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1213]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1224,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | l1_pre_topc(k8_tmap_1(X0,X1))
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1225,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1224]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3718,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3716,c_30,c_29,c_28,c_1214,c_1225]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3719,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3718]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4762,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3719]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5954,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4762]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2758,plain,
% 3.02/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2759,plain,
% 3.02/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2758]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4781,plain,
% 3.02/1.02      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,X0_56) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_2759]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4812,plain,
% 3.02/1.02      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | k7_tmap_1(sK3,X0_56) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | ~ sP0_iProver_split ),
% 3.02/1.02      inference(splitting,
% 3.02/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.02/1.02                [c_4781]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5939,plain,
% 3.02/1.02      ( k7_tmap_1(sK3,X0_56) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.02/1.02      | sP0_iProver_split != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4812]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9539,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | sP0_iProver_split != iProver_top ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5954,c_5939]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4813,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3) | ~ l1_pre_topc(sK3) | sP0_iProver_split ),
% 3.02/1.02      inference(splitting,
% 3.02/1.02                [splitting(split),new_symbols(definition,[])],
% 3.02/1.02                [c_4781]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4887,plain,
% 3.02/1.02      ( v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | sP0_iProver_split = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4813]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9871,plain,
% 3.02/1.02      ( l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,[status(thm)],[c_9539,c_4887]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9872,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_9871]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1235,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v1_pre_topc(X2)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X2)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | k8_tmap_1(X0,X1) = X2
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1236,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1235]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1240,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1236,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1241,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_1240]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_995,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(X0,X1))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | X2 != X0
% 3.02/1.02      | X2 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_996,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_995]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2338,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_996,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2339,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2338]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3847,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1241,c_2339]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3848,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3847]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1031,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | l1_pre_topc(k8_tmap_1(X0,X2))
% 3.02/1.02      | X1 != X0
% 3.02/1.02      | X1 != X2 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1032,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | l1_pre_topc(k8_tmap_1(X0,X0)) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1031]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2312,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | l1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1032,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2313,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2312]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1013,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_pre_topc(k8_tmap_1(X0,X1))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | X2 != X0
% 3.02/1.02      | X2 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1014,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1013]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2325,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1014,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2326,plain,
% 3.02/1.02      ( v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2325]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3850,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3848,c_2313,c_2326]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3851,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3850]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4756,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3851]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5960,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4756]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9677,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5960,c_5940]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2486,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v1_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k8_tmap_1(X0,X0) = X1
% 3.02/1.02      | sK2 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1050,c_30]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2487,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2486]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2491,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2487,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2492,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_2491]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3785,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2492,c_2339]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3786,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3785]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3788,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3786,c_2313,c_2326]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3789,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3788]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4759,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3789]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5957,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4759]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9546,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5957,c_5940]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2533,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_996,c_30]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2534,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2533]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2536,plain,
% 3.02/1.02      ( v1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2534,c_30,c_29,c_28,c_39,c_63]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3583,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2536,c_2286]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3584,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3583]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3586,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3584,c_30,c_29,c_28,c_39,c_66,c_69]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3587,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3586]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4771,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3587]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5949,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | m1_subset_1(sK0(sK3,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4771]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9163,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | sP0_iProver_split != iProver_top ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5949,c_5939]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9201,plain,
% 3.02/1.02      ( l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(global_propositional_subsumption,[status(thm)],[c_9163,c_4887]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9202,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_9201]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3701,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2492,c_1205]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3702,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3701]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1881,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k8_tmap_1(X0,X0) = X1
% 3.02/1.02      | k8_tmap_1(sK2,sK3) != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1050,c_1205]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1882,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X0,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1881]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1886,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | m1_subset_1(sK0(X0,X0,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1882,c_30,c_29,c_28,c_1214,c_1225]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1887,plain,
% 3.02/1.02      ( m1_subset_1(sK0(X0,X0,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_1886]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1889,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_1887]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3704,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3702,c_30,c_29,c_28,c_1889]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4763,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3704]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5953,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK2,k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4763]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_9059,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5953,c_5940]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3625,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2536,c_1241]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3626,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3625]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1683,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k8_tmap_1(X1,X1) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1241,c_996]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1684,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(X0,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1683]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1688,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(X0,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1684,c_1014,c_1032]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1689,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(X0,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_1688]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1691,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_1689]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3628,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3626,c_30,c_29,c_28,c_1691]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4768,plain,
% 3.02/1.02      ( m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3628]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5950,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | m1_subset_1(sK0(sK2,sK3,k8_tmap_1(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4768]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8986,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5950,c_5940]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3,plain,
% 3.02/1.02      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.02/1.02      | ~ v1_funct_2(X5,X2,X3)
% 3.02/1.02      | ~ v1_funct_2(X4,X0,X1)
% 3.02/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.02/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/1.02      | ~ v1_funct_1(X5)
% 3.02/1.02      | ~ v1_funct_1(X4)
% 3.02/1.02      | v1_xboole_0(X1)
% 3.02/1.02      | v1_xboole_0(X3)
% 3.02/1.02      | X4 = X5 ),
% 3.02/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3157,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X3,X4,X5)
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X3)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | v1_xboole_0(X5)
% 3.02/1.02      | X3 = X0
% 3.02/1.02      | k9_tmap_1(sK2,sK2) != X0
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != X3
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) != X5
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK2,sK2)) != X2
% 3.02/1.02      | u1_struct_0(sK2) != X4
% 3.02/1.02      | u1_struct_0(sK2) != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_2631]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3158,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3157]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2039,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X3,X4,X5)
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(X6,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(k8_tmap_1(X6,X6)))))
% 3.02/1.02      | ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(u1_struct_0(X6)))
% 3.02/1.02      | ~ v2_pre_topc(X6)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X3)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(X6,X6))
% 3.02/1.02      | v2_struct_0(X6)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | v1_xboole_0(X5)
% 3.02/1.02      | ~ l1_pre_topc(X6)
% 3.02/1.02      | X3 = X0
% 3.02/1.02      | k9_tmap_1(X6,X6) != X0
% 3.02/1.02      | k7_tmap_1(X6,u1_struct_0(X6)) != X3
% 3.02/1.02      | u1_struct_0(X6) != X4
% 3.02/1.02      | u1_struct_0(X6) != X1
% 3.02/1.02      | u1_struct_0(k6_tmap_1(X6,u1_struct_0(X6))) != X5
% 3.02/1.02      | u1_struct_0(k8_tmap_1(X6,X6)) != X2 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_761]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2040,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(X0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))))
% 3.02/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(X0,X0))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(X0,u1_struct_0(X0)))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k7_tmap_1(X0,u1_struct_0(X0)) = k9_tmap_1(X0,X0) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2039]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2044,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(X0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(X0,u1_struct_0(X0)))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k7_tmap_1(X0,u1_struct_0(X0)) = k9_tmap_1(X0,X0) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2040,c_788,c_930,c_960,c_978]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2045,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(X0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(X0,u1_struct_0(X0)))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k7_tmap_1(X0,u1_struct_0(X0)) = k9_tmap_1(X0,X0) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_2044]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2047,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_2045]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3160,plain,
% 3.02/1.02      ( ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3158,c_30,c_29,c_28,c_2047]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3161,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3160]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4461,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3161,c_2365]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4734,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4461]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5982,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4734]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6416,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5982,c_4784,c_4786]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6424,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_6416,c_5937]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8850,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_6424,c_7398]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1189,plain,
% 3.02/1.02      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1190,plain,
% 3.02/1.02      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1189]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1192,plain,
% 3.02/1.02      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1190,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1176,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1177,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK2)
% 3.02/1.02      | v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1176]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1179,plain,
% 3.02/1.02      ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1177,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_835,plain,
% 3.02/1.02      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.02/1.02      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_203,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_836,plain,
% 3.02/1.02      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_835]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_838,plain,
% 3.02/1.02      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_836,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_839,plain,
% 3.02/1.02      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_838]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1165,plain,
% 3.02/1.02      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.02/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1158,c_839]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1186,plain,
% 3.02/1.02      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 3.02/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1179,c_1165]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1199,plain,
% 3.02/1.02      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 3.02/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1192,c_1186]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3183,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X3,X4,X5)
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X3)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | v1_xboole_0(X5)
% 3.02/1.02      | X3 = X0
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
% 3.02/1.02      | u1_struct_0(sK2) != X4
% 3.02/1.02      | u1_struct_0(sK2) != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_1199]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3184,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3183]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2078,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X3,X4,X5)
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X3)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | v1_xboole_0(X5)
% 3.02/1.02      | X3 = X0
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
% 3.02/1.02      | u1_struct_0(sK2) != X4
% 3.02/1.02      | u1_struct_0(sK2) != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_1199]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2079,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2078]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_855,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_856,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_855]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2081,plain,
% 3.02/1.02      ( ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2079,c_30,c_29,c_28,c_856,c_1177,c_1190]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2082,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_2081]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3186,plain,
% 3.02/1.02      ( ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3184,c_30,c_29,c_28,c_856,c_1177,c_1190,c_2079]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3187,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3186]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4392,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2558,c_3187]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4737,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4392]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5979,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4737]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6356,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5979,c_4803,c_4806]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6362,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_6356,c_5937]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4816,plain,( X0_57 = X0_57 ),theory(equality) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4861,plain,
% 3.02/1.02      ( sK2 = sK2 ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_4816]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_19,plain,
% 3.02/1.02      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.02/1.02      | ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1) ),
% 3.02/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_190,plain,
% 3.02/1.02      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.02      | ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1) ),
% 3.02/1.02      inference(global_propositional_subsumption,[status(thm)],[c_19,c_22]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_191,plain,
% 3.02/1.02      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.02/1.02      | ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_190]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_24,negated_conjecture,
% 3.02/1.02      ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
% 3.02/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_396,plain,
% 3.02/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | sK4 != X2
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_191,c_24]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_397,plain,
% 3.02/1.02      ( ~ m1_pre_topc(sK3,X0)
% 3.02/1.02      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | v2_struct_0(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_396]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_25,negated_conjecture,
% 3.02/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.02/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_401,plain,
% 3.02/1.02      ( v2_struct_0(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ m1_pre_topc(sK3,X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_397,c_27,c_25]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_402,plain,
% 3.02/1.02      ( ~ m1_pre_topc(sK3,X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_401]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1450,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | sK2 != X0
% 3.02/1.02      | sK3 != sK3 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_402]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1451,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1450]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_404,plain,
% 3.02/1.02      ( ~ m1_pre_topc(sK3,sK2)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_402]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1453,plain,
% 3.02/1.02      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1451,c_30,c_29,c_28,c_26,c_404,c_1140]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4798,plain,
% 3.02/1.02      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_1453]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4838,plain,
% 3.02/1.02      ( k2_tmap_1(X0_57,X1_57,X0_56,X2_57) = k2_tmap_1(X3_57,X4_57,X1_56,X5_57)
% 3.02/1.02      | X0_57 != X3_57
% 3.02/1.02      | X1_57 != X4_57
% 3.02/1.02      | X2_57 != X5_57
% 3.02/1.02      | X0_56 != X1_56 ),
% 3.02/1.02      theory(equality) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6879,plain,
% 3.02/1.02      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.02      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | sK2 != sK2
% 3.02/1.02      | sK3 != sK3
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_4838]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6919,plain,
% 3.02/1.02      ( sK3 = sK3 ),
% 3.02/1.02      inference(instantiation,[status(thm)],[c_4816]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8788,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK2)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_6362,c_4861,c_4806,c_4798,c_6879,c_6919]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8792,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK2) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_8788,c_7296]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8857,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_8850,c_8792]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4440,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3161,c_1179]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4735,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4440]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5981,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))))) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4735]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6367,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5981,c_4784,c_4786]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6373,plain,
% 3.02/1.02      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k9_tmap_1(sK2,sK2)
% 3.02/1.02      | k7_tmap_1(sK2,u1_struct_0(sK2)) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_6367,c_5937]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8798,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_6373,c_7398]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8803,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK3) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_8798,c_8792]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6105,plain,
% 3.02/1.02      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_4798,c_4806]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8139,plain,
% 3.02/1.02      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.02/1.02      inference(demodulation,[status(thm)],[c_7296,c_6105]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2416,plain,
% 3.02/1.02      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 3.02/1.02      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_funct_1(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k9_tmap_1(X0,X0) = X1
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_806,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2417,plain,
% 3.02/1.02      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2416]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3306,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1199,c_2417]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3307,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3306]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3309,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3307,c_30,c_29,c_28,c_1177]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3310,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3309]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4777,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3310]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5943,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4777]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6481,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5943,c_4803,c_4806]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_8138,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(demodulation,[status(thm)],[c_7296,c_6481]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_7484,plain,
% 3.02/1.02      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | sP0_iProver_split != iProver_top ),
% 3.02/1.02      inference(superposition,[status(thm)],[c_5919,c_5939]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3054,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X0,X3,X4)
% 3.02/1.02      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.02/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X5)
% 3.02/1.02      | v1_xboole_0(X4)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | X5 != X0
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X5
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,X5)) != X0
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X5))) != X2
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK2,sK3)) != X4
% 3.02/1.02      | u1_struct_0(sK2) != X1
% 3.02/1.02      | u1_struct_0(sK2) != X3 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_872]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3055,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3054]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4313,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != X0
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3055,c_2365]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4314,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4313]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4740,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4314]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5976,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4740]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6629,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5976,c_4803]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6640,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_6629,c_5937]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3367,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != X0
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_872,c_2471]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3368,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3367]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3370,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,[status(thm)],[c_3368,c_2365]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3371,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3370]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4775,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3371]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5945,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4775]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6500,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3))) != k7_tmap_1(sK3,u1_struct_0(sK3))
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK3,sK3)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(sK2)
% 3.02/1.02      | u1_struct_0(sK2) != u1_struct_0(sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5945,c_4803]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1376,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.02/1.02      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k9_tmap_1(X1,X2) = X0
% 3.02/1.02      | sK2 != X1
% 3.02/1.02      | sK3 != X2 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1377,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1376]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1381,plain,
% 3.02/1.02      ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1377,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1382,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_1381]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4369,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1382,c_2365]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4370,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4369]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4738,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4370]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5978,plain,
% 3.02/1.02      ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4738]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6343,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(sK1(sK2,sK3,k9_tmap_1(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5978,c_4803]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4347,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1409,c_2365]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4348,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4347]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4739,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4348]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5977,plain,
% 3.02/1.02      ( sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4739]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6293,plain,
% 3.02/1.02      ( sK1(sK2,sK3,k9_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5977,c_4803]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4802,plain,
% 3.02/1.02      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_1192]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5921,plain,
% 3.02/1.02      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4802]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6029,plain,
% 3.02/1.02      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5921,c_4803]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_858,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_856,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4808,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_858]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5918,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4808]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6015,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.02/1.02      inference(light_normalisation,[status(thm)],[c_5918,c_4803]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3209,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X3,X4,X5)
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X3)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | v1_xboole_0(X5)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | X3 = X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) != X0
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) != X3
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))) != X5
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != X2
% 3.02/1.02      | u1_struct_0(sK3) != X4
% 3.02/1.02      | u1_struct_0(sK3) != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_2471]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3210,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(k9_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3209]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2443,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_788,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2444,plain,
% 3.02/1.02      ( v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2443]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3212,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3210,c_2352,c_2365,c_2444]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3213,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3)))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_3212]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4489,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1179,c_3213]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4733,plain,
% 3.02/1.02      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4489]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5983,plain,
% 3.02/1.02      ( k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k9_tmap_1(sK3,sK3)
% 3.02/1.02      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))) != iProver_top
% 3.02/1.02      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4733]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2650,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.02      | k9_tmap_1(X1,X1) = X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1347,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2651,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2650]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4201,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2651,c_1179]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4202,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK3,sK3,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4201]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4744,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK1(sK3,sK3,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4202]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5972,plain,
% 3.02/1.02      ( sK1(sK3,sK3,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4744]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2677,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.02/1.02      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k9_tmap_1(X1,X1) = X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1317,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2678,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2677]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4179,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2678,c_1179]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4180,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4179]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4745,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4180]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5971,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4745]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3085,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.02      | ~ v1_funct_2(X0,X3,X4)
% 3.02/1.02      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.02/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | ~ v1_funct_1(X5)
% 3.02/1.02      | v1_xboole_0(X4)
% 3.02/1.02      | v1_xboole_0(X2)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | X5 != X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X5
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,X5)) != X0
% 3.02/1.02      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X5))) != X2
% 3.02/1.02      | u1_struct_0(k8_tmap_1(sK3,sK3)) != X4
% 3.02/1.02      | u1_struct_0(sK3) != X1
% 3.02/1.02      | u1_struct_0(sK3) != X3 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_2417]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3086,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ v1_funct_1(X0)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3085]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4113,plain,
% 3.02/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
% 3.02/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))))
% 3.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = X0
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_3086,c_1179]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4114,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_4113]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4748,plain,
% 3.02/1.02      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
% 3.02/1.02      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))))
% 3.02/1.02      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3)))))
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k9_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_4114]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5968,plain,
% 3.02/1.02      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK2,sK3)
% 3.02/1.02      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))) != k9_tmap_1(sK2,sK3)
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))))) != iProver_top
% 3.02/1.02      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))))))) != iProver_top
% 3.02/1.02      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK2,sK3))))) = iProver_top
% 3.02/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4748]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_6,plain,
% 3.02/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | ~ v1_pre_topc(X2)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X2)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | sK0(X1,X0,X2) = u1_struct_0(X0)
% 3.02/1.02      | k8_tmap_1(X1,X0) = X2 ),
% 3.02/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1262,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK0(X1,X2,X0) = u1_struct_0(X2)
% 3.02/1.02      | k8_tmap_1(X1,X2) = X0
% 3.02/1.02      | sK2 != X1
% 3.02/1.02      | sK3 != X2 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1263,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1262]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1267,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1263,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1268,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_1267]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3827,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1268,c_2339]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3828,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3827]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3830,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3828,c_2313,c_2326]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4757,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3830]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5959,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | sK0(sK2,sK3,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4757]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5,plain,
% 3.02/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.02      | ~ v1_pre_topc(X2)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X2)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
% 3.02/1.02      | k8_tmap_1(X1,X0) = X2 ),
% 3.02/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1289,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
% 3.02/1.02      | k8_tmap_1(X1,X2) = X0
% 3.02/1.02      | sK2 != X1
% 3.02/1.02      | sK3 != X2 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_26]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1290,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | v2_struct_0(sK2)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1289]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1294,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_1290,c_30,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1295,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_1294]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3807,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1295,c_2339]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3808,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3807]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3810,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3808,c_2313,c_2326]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4758,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3810]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5958,plain,
% 3.02/1.02      ( k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4758]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1109,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | X2 != X1
% 3.02/1.02      | X2 != X3
% 3.02/1.02      | k6_tmap_1(X1,sK0(X1,X3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(X1,X3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1110,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
% 3.02/1.02      | k8_tmap_1(X1,X1) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1109]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2830,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
% 3.02/1.02      | k8_tmap_1(X1,X1) = X0
% 3.02/1.02      | sK2 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1110,c_30]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2831,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2830]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2835,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2831,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2836,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_2835]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3761,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2836,c_2339]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3762,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3761]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3764,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3762,c_2313,c_2326]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4760,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3764]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5956,plain,
% 3.02/1.02      ( k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK3,sK3))) != k8_tmap_1(sK3,sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4760]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1079,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X2)
% 3.02/1.02      | X2 != X1
% 3.02/1.02      | X2 != X3
% 3.02/1.02      | sK0(X1,X3,X0) = u1_struct_0(X3)
% 3.02/1.02      | k8_tmap_1(X1,X3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_1080,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | v2_struct_0(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | sK0(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.02      | k8_tmap_1(X1,X1) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_1079]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2855,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | sK0(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.02      | k8_tmap_1(X1,X1) = X0
% 3.02/1.02      | sK2 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1080,c_30]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2856,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK2)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK2)
% 3.02/1.02      | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2855]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2860,plain,
% 3.02/1.02      ( ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_2856,c_29,c_28]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2861,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0 ),
% 3.02/1.02      inference(renaming,[status(thm)],[c_2860]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3741,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2861,c_2339]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3742,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3741]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3744,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3742,c_2313,c_2326]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4761,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3744]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5955,plain,
% 3.02/1.02      ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | sK0(sK2,sK2,k8_tmap_1(sK3,sK3)) = u1_struct_0(sK2)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4761]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2704,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
% 3.02/1.02      | k8_tmap_1(X1,X1) = X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1110,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2705,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2704]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3681,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2705,c_1205]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3682,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3681]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3684,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3682,c_30,c_29,c_28,c_1214,c_1225]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4764,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3684]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5952,plain,
% 3.02/1.02      ( k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4764]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2731,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X1)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X1)
% 3.02/1.02      | sK0(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.02      | k8_tmap_1(X1,X1) = X0
% 3.02/1.02      | sK3 != X1 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_1080,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2732,plain,
% 3.02/1.02      ( ~ v1_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2731]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3661,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK3) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2732,c_1205]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3662,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3661]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3664,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3662,c_30,c_29,c_28,c_1214,c_1225]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4765,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3664]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5951,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK3)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4765]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3561,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,X0)) != X0
% 3.02/1.02      | k8_tmap_1(sK2,sK2) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2536,c_2705]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3562,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3561]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3564,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3562,c_30,c_29,c_28,c_39,c_66,c_69]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4772,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3564]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5948,plain,
% 3.02/1.02      ( k6_tmap_1(sK3,sK0(sK3,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4772]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3541,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK2,sK2) != X0
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_2536,c_2732]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3542,plain,
% 3.02/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_3541]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_3544,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.02      inference(global_propositional_subsumption,
% 3.02/1.02                [status(thm)],
% 3.02/1.02                [c_3542,c_30,c_29,c_28,c_39,c_66,c_69]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4773,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_3544]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5947,plain,
% 3.02/1.02      ( k8_tmap_1(sK3,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.02      | sK0(sK3,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4773]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5938,plain,
% 3.02/1.02      ( v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.02/1.02      | sP0_iProver_split = iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4813]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2403,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
% 3.02/1.02      | sK3 != X0 ),
% 3.02/1.02      inference(resolution_lifted,[status(thm)],[c_894,c_27]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2404,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(unflattening,[status(thm)],[c_2403]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_4792,plain,
% 3.02/1.02      ( ~ v2_pre_topc(sK3)
% 3.02/1.02      | ~ l1_pre_topc(sK3)
% 3.02/1.02      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 3.02/1.02      inference(subtyping,[status(esa)],[c_2404]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5930,plain,
% 3.02/1.02      ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3)
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4792]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_5929,plain,
% 3.02/1.02      ( k5_tmap_1(sK3,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.02      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4793]) ).
% 3.02/1.02  
% 3.02/1.02  cnf(c_2377,plain,
% 3.02/1.02      ( ~ v2_pre_topc(X0)
% 3.02/1.02      | ~ l1_pre_topc(X0)
% 3.02/1.02      | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0)
% 3.02/1.03      | sK3 != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_942,c_27]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2378,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3)
% 3.02/1.03      | u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_2377]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4794,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3)
% 3.02/1.03      | u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2378]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5928,plain,
% 3.02/1.03      ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 3.02/1.03      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4794]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1430,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X1)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | X0 != X1
% 3.02/1.03      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.03      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | sK3 != X1 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_402]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1431,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK3)
% 3.02/1.03      | v2_struct_0(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3)
% 3.02/1.03      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.03      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_1430]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1433,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3)
% 3.02/1.03      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.03      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1431,c_27]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4799,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3)
% 3.02/1.03      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.03      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_1433]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5924,plain,
% 3.02/1.03      ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK3)),k7_tmap_1(sK3,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.02/1.03      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4799]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3603,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
% 3.02/1.03      | k8_tmap_1(sK2,sK2) != X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_2536,c_1295]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3604,plain,
% 3.02/1.03      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_3603]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1629,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(X1)
% 3.02/1.03      | v2_struct_0(X1)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X1)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
% 3.02/1.03      | k8_tmap_1(X1,X1) != X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_1295,c_996]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1630,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(X0,X0))) != k8_tmap_1(X0,X0)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_1629]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1634,plain,
% 3.02/1.03      ( ~ l1_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ v2_pre_topc(X0)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(X0,X0))) != k8_tmap_1(X0,X0)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1630,c_1014,c_1032]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1635,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(X0,X0))) != k8_tmap_1(X0,X0)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_1634]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1637,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK2)
% 3.02/1.03      | v2_struct_0(sK2)
% 3.02/1.03      | ~ l1_pre_topc(sK2)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(instantiation,[status(thm)],[c_1635]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3606,plain,
% 3.02/1.03      ( k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_3604,c_30,c_29,c_28,c_1637]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4770,plain,
% 3.02/1.03      ( k6_tmap_1(sK2,sK0(sK2,sK3,k8_tmap_1(sK2,sK2))) != k8_tmap_1(sK2,sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_3606]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3614,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) != X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_2536,c_1268]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3615,plain,
% 3.02/1.03      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.03      | sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_3614]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1656,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(X1)
% 3.02/1.03      | v2_struct_0(X1)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X1)
% 3.02/1.03      | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(X1,X1) != X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_1268,c_996]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1657,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.03      | sK0(sK2,sK3,k8_tmap_1(X0,X0)) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_1656]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1661,plain,
% 3.02/1.03      ( ~ l1_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ v2_pre_topc(X0)
% 3.02/1.03      | sK0(sK2,sK3,k8_tmap_1(X0,X0)) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1657,c_1014,c_1032]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1662,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | sK0(sK2,sK3,k8_tmap_1(X0,X0)) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0,X0) ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_1661]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1664,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK2)
% 3.02/1.03      | v2_struct_0(sK2)
% 3.02/1.03      | ~ l1_pre_topc(sK2)
% 3.02/1.03      | sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(instantiation,[status(thm)],[c_1662]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3617,plain,
% 3.02/1.03      ( sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_3615,c_30,c_29,c_28,c_1664]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4769,plain,
% 3.02/1.03      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK2)
% 3.02/1.03      | sK0(sK2,sK3,k8_tmap_1(sK2,sK2)) = u1_struct_0(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_3617]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3639,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | sK0(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_2861,c_1205]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3640,plain,
% 3.02/1.03      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_3639]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1817,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(X1)
% 3.02/1.03      | v2_struct_0(X1)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X1)
% 3.02/1.03      | sK0(X1,X1,X0) = u1_struct_0(X1)
% 3.02/1.03      | k8_tmap_1(X1,X1) = X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_1080,c_1205]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1818,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | sK0(X0,X0,k8_tmap_1(sK2,sK3)) = u1_struct_0(X0)
% 3.02/1.03      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_1817]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1822,plain,
% 3.02/1.03      ( ~ l1_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ v2_pre_topc(X0)
% 3.02/1.03      | sK0(X0,X0,k8_tmap_1(sK2,sK3)) = u1_struct_0(X0)
% 3.02/1.03      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1818,c_30,c_29,c_28,c_1214,c_1225]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1823,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | sK0(X0,X0,k8_tmap_1(sK2,sK3)) = u1_struct_0(X0)
% 3.02/1.03      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_1822]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1825,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK2)
% 3.02/1.03      | v2_struct_0(sK2)
% 3.02/1.03      | ~ l1_pre_topc(sK2)
% 3.02/1.03      | sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(instantiation,[status(thm)],[c_1823]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3642,plain,
% 3.02/1.03      ( sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_3640,c_30,c_29,c_28,c_1825]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4767,plain,
% 3.02/1.03      ( k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3)
% 3.02/1.03      | sK0(sK2,sK2,k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_3642]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3650,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK2,X0)) != X0
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_2836,c_1205]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3651,plain,
% 3.02/1.03      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_3650]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1790,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(X1)
% 3.02/1.03      | v2_struct_0(X1)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X1)
% 3.02/1.03      | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
% 3.02/1.03      | k8_tmap_1(X1,X1) = X0
% 3.02/1.03      | k8_tmap_1(sK2,sK3) != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_1110,c_1205]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1791,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.02/1.03      | k6_tmap_1(X0,sK0(X0,X0,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_1790]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1795,plain,
% 3.02/1.03      ( ~ l1_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ v2_pre_topc(X0)
% 3.02/1.03      | k6_tmap_1(X0,sK0(X0,X0,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1791,c_30,c_29,c_28,c_1214,c_1225]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1796,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | v2_struct_0(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | k6_tmap_1(X0,sK0(X0,X0,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(X0,X0) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_1795]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1798,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK2)
% 3.02/1.03      | v2_struct_0(sK2)
% 3.02/1.03      | ~ l1_pre_topc(sK2)
% 3.02/1.03      | k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(instantiation,[status(thm)],[c_1796]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3653,plain,
% 3.02/1.03      ( k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_3651,c_30,c_29,c_28,c_1798]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4766,plain,
% 3.02/1.03      ( k6_tmap_1(sK2,sK0(sK2,sK2,k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 3.02/1.03      | k8_tmap_1(sK2,sK2) = k8_tmap_1(sK2,sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_3653]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2522,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | v2_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | sK2 != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_1014,c_30]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2523,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.03      | ~ v2_pre_topc(sK2)
% 3.02/1.03      | ~ l1_pre_topc(sK2) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_2522]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2525,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_2523,c_30,c_29,c_28,c_39,c_66]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4788,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2525]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5934,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4788]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2511,plain,
% 3.02/1.03      ( ~ v2_pre_topc(X0)
% 3.02/1.03      | ~ l1_pre_topc(X0)
% 3.02/1.03      | l1_pre_topc(k8_tmap_1(X0,X0))
% 3.02/1.03      | sK2 != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_1032,c_30]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2512,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK2)
% 3.02/1.03      | l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.02/1.03      | ~ l1_pre_topc(sK2) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_2511]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2514,plain,
% 3.02/1.03      ( l1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_2512,c_30,c_29,c_28,c_39,c_69]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4789,plain,
% 3.02/1.03      ( l1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2514]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5933,plain,
% 3.02/1.03      ( l1_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4789]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2476,plain,
% 3.02/1.03      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK3 != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_378,c_27]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2477,plain,
% 3.02/1.03      ( ~ v1_xboole_0(u1_struct_0(sK3)) | ~ l1_pre_topc(sK3) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_2476]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4790,plain,
% 3.02/1.03      ( ~ v1_xboole_0(u1_struct_0(sK3)) | ~ l1_pre_topc(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2477]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5932,plain,
% 3.02/1.03      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4790]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4791,plain,
% 3.02/1.03      ( v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 3.02/1.03      | ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2444]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5931,plain,
% 3.02/1.03      ( v1_funct_2(k9_tmap_1(sK3,sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
% 3.02/1.03      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4791]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4795,plain,
% 3.02/1.03      ( m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 3.02/1.03      | ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2352]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5927,plain,
% 3.02/1.03      ( m1_subset_1(k9_tmap_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top
% 3.02/1.03      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4795]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4796,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.03      | ~ v2_pre_topc(sK3)
% 3.02/1.03      | ~ l1_pre_topc(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2326]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5926,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK3,sK3)) = iProver_top
% 3.02/1.03      | v2_pre_topc(sK3) != iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4796]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4797,plain,
% 3.02/1.03      ( ~ v2_pre_topc(sK3)
% 3.02/1.03      | l1_pre_topc(k8_tmap_1(sK3,sK3))
% 3.02/1.03      | ~ l1_pre_topc(sK3) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_2313]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5925,plain,
% 3.02/1.03      ( v2_pre_topc(sK3) != iProver_top
% 3.02/1.03      | l1_pre_topc(k8_tmap_1(sK3,sK3)) = iProver_top
% 3.02/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4797]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1227,plain,
% 3.02/1.03      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1225,c_30,c_29,c_28]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4800,plain,
% 3.02/1.03      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_1227]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5923,plain,
% 3.02/1.03      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4800]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1216,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1214,c_30,c_29,c_28]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4801,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_1216]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5922,plain,
% 3.02/1.03      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4801]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4811,negated_conjecture,
% 3.02/1.03      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5915,plain,
% 3.02/1.03      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4811]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4810,negated_conjecture,
% 3.02/1.03      ( l1_pre_topc(sK2) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_28]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5916,plain,
% 3.02/1.03      ( l1_pre_topc(sK2) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4810]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4809,negated_conjecture,
% 3.02/1.03      ( v2_pre_topc(sK2) ),
% 3.02/1.03      inference(subtyping,[status(esa)],[c_29]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5917,plain,
% 3.02/1.03      ( v2_pre_topc(sK2) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4809]) ).
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  % SZS output end Saturation for theBenchmark.p
% 3.02/1.03  
% 3.02/1.03  ------                               Statistics
% 3.02/1.03  
% 3.02/1.03  ------ General
% 3.02/1.03  
% 3.02/1.03  abstr_ref_over_cycles:                  0
% 3.02/1.03  abstr_ref_under_cycles:                 0
% 3.02/1.03  gc_basic_clause_elim:                   0
% 3.02/1.03  forced_gc_time:                         0
% 3.02/1.03  parsing_time:                           0.011
% 3.02/1.03  unif_index_cands_time:                  0.
% 3.02/1.03  unif_index_add_time:                    0.
% 3.02/1.03  orderings_time:                         0.
% 3.02/1.03  out_proof_time:                         0.
% 3.02/1.03  total_time:                             0.343
% 3.02/1.03  num_of_symbols:                         67
% 3.02/1.03  num_of_terms:                           6415
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing
% 3.02/1.03  
% 3.02/1.03  num_of_splits:                          1
% 3.02/1.03  num_of_split_atoms:                     1
% 3.02/1.03  num_of_reused_defs:                     0
% 3.02/1.03  num_eq_ax_congr_red:                    10
% 3.02/1.03  num_of_sem_filtered_clauses:            8
% 3.02/1.03  num_of_subtypes:                        4
% 3.02/1.03  monotx_restored_types:                  0
% 3.02/1.03  sat_num_of_epr_types:                   0
% 3.02/1.03  sat_num_of_non_cyclic_types:            0
% 3.02/1.03  sat_guarded_non_collapsed_types:        0
% 3.02/1.03  num_pure_diseq_elim:                    0
% 3.02/1.03  simp_replaced_by:                       0
% 3.02/1.03  res_preprocessed:                       239
% 3.02/1.03  prep_upred:                             0
% 3.02/1.03  prep_unflattend:                        276
% 3.02/1.03  smt_new_axioms:                         0
% 3.02/1.03  pred_elim_cands:                        12
% 3.02/1.03  pred_elim:                              7
% 3.02/1.03  pred_elim_cl:                           -49
% 3.02/1.03  pred_elim_cycles:                       12
% 3.02/1.03  merged_defs:                            0
% 3.02/1.03  merged_defs_ncl:                        0
% 3.02/1.03  bin_hyper_res:                          0
% 3.02/1.03  prep_cycles:                            3
% 3.02/1.03  pred_elim_time:                         0.106
% 3.02/1.03  splitting_time:                         0.
% 3.02/1.03  sem_filter_time:                        0.
% 3.02/1.03  monotx_time:                            0.
% 3.02/1.03  subtype_inf_time:                       0.001
% 3.02/1.03  
% 3.02/1.03  ------ Problem properties
% 3.02/1.03  
% 3.02/1.03  clauses:                                81
% 3.02/1.03  conjectures:                            3
% 3.02/1.03  epr:                                    3
% 3.02/1.03  horn:                                   45
% 3.02/1.03  ground:                                 78
% 3.02/1.03  unary:                                  20
% 3.02/1.03  binary:                                 9
% 3.02/1.03  lits:                                   329
% 3.02/1.03  lits_eq:                                114
% 3.02/1.03  fd_pure:                                0
% 3.02/1.03  fd_pseudo:                              0
% 3.02/1.03  fd_cond:                                0
% 3.02/1.03  fd_pseudo_cond:                         0
% 3.02/1.03  ac_symbols:                             0
% 3.02/1.03  
% 3.02/1.03  ------ Propositional Solver
% 3.02/1.03  
% 3.02/1.03  prop_solver_calls:                      24
% 3.02/1.03  prop_fast_solver_calls:                 3622
% 3.02/1.03  smt_solver_calls:                       0
% 3.02/1.03  smt_fast_solver_calls:                  0
% 3.02/1.03  prop_num_of_clauses:                    2088
% 3.02/1.03  prop_preprocess_simplified:             7183
% 3.02/1.03  prop_fo_subsumed:                       189
% 3.02/1.03  prop_solver_time:                       0.
% 3.02/1.03  smt_solver_time:                        0.
% 3.02/1.03  smt_fast_solver_time:                   0.
% 3.02/1.03  prop_fast_solver_time:                  0.
% 3.02/1.03  prop_unsat_core_time:                   0.
% 3.02/1.03  
% 3.02/1.03  ------ QBF
% 3.02/1.03  
% 3.02/1.03  qbf_q_res:                              0
% 3.02/1.03  qbf_num_tautologies:                    0
% 3.02/1.03  qbf_prep_cycles:                        0
% 3.02/1.03  
% 3.02/1.03  ------ BMC1
% 3.02/1.03  
% 3.02/1.03  bmc1_current_bound:                     -1
% 3.02/1.03  bmc1_last_solved_bound:                 -1
% 3.02/1.03  bmc1_unsat_core_size:                   -1
% 3.02/1.03  bmc1_unsat_core_parents_size:           -1
% 3.02/1.03  bmc1_merge_next_fun:                    0
% 3.02/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.03  
% 3.02/1.03  ------ Instantiation
% 3.02/1.03  
% 3.02/1.03  inst_num_of_clauses:                    617
% 3.02/1.03  inst_num_in_passive:                    147
% 3.02/1.03  inst_num_in_active:                     438
% 3.02/1.03  inst_num_in_unprocessed:                34
% 3.02/1.03  inst_num_of_loops:                      470
% 3.02/1.03  inst_num_of_learning_restarts:          0
% 3.02/1.03  inst_num_moves_active_passive:          28
% 3.02/1.03  inst_lit_activity:                      0
% 3.02/1.03  inst_lit_activity_moves:                0
% 3.02/1.03  inst_num_tautologies:                   0
% 3.02/1.03  inst_num_prop_implied:                  0
% 3.02/1.03  inst_num_existing_simplified:           0
% 3.02/1.03  inst_num_eq_res_simplified:             0
% 3.02/1.03  inst_num_child_elim:                    0
% 3.02/1.03  inst_num_of_dismatching_blockings:      502
% 3.02/1.03  inst_num_of_non_proper_insts:           782
% 3.02/1.03  inst_num_of_duplicates:                 0
% 3.02/1.03  inst_inst_num_from_inst_to_res:         0
% 3.02/1.03  inst_dismatching_checking_time:         0.
% 3.02/1.03  
% 3.02/1.03  ------ Resolution
% 3.02/1.03  
% 3.02/1.03  res_num_of_clauses:                     0
% 3.02/1.03  res_num_in_passive:                     0
% 3.02/1.03  res_num_in_active:                      0
% 3.02/1.03  res_num_of_loops:                       242
% 3.02/1.03  res_forward_subset_subsumed:            155
% 3.02/1.03  res_backward_subset_subsumed:           4
% 3.02/1.03  res_forward_subsumed:                   0
% 3.02/1.03  res_backward_subsumed:                  0
% 3.02/1.03  res_forward_subsumption_resolution:     19
% 3.02/1.03  res_backward_subsumption_resolution:    3
% 3.02/1.03  res_clause_to_clause_subsumption:       1032
% 3.02/1.03  res_orphan_elimination:                 0
% 3.02/1.03  res_tautology_del:                      141
% 3.02/1.03  res_num_eq_res_simplified:              0
% 3.02/1.03  res_num_sel_changes:                    0
% 3.02/1.03  res_moves_from_active_to_pass:          0
% 3.02/1.03  
% 3.02/1.03  ------ Superposition
% 3.02/1.03  
% 3.02/1.03  sup_time_total:                         0.
% 3.02/1.03  sup_time_generating:                    0.
% 3.02/1.03  sup_time_sim_full:                      0.
% 3.02/1.03  sup_time_sim_immed:                     0.
% 3.02/1.03  
% 3.02/1.03  sup_num_of_clauses:                     75
% 3.02/1.03  sup_num_in_active:                      75
% 3.02/1.03  sup_num_in_passive:                     0
% 3.02/1.03  sup_num_of_loops:                       93
% 3.02/1.03  sup_fw_superposition:                   13
% 3.02/1.03  sup_bw_superposition:                   9
% 3.02/1.03  sup_immediate_simplified:               10
% 3.02/1.03  sup_given_eliminated:                   0
% 3.02/1.03  comparisons_done:                       0
% 3.02/1.03  comparisons_avoided:                    25
% 3.02/1.03  
% 3.02/1.03  ------ Simplifications
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  sim_fw_subset_subsumed:                 4
% 3.02/1.03  sim_bw_subset_subsumed:                 11
% 3.02/1.03  sim_fw_subsumed:                        0
% 3.02/1.03  sim_bw_subsumed:                        0
% 3.02/1.03  sim_fw_subsumption_res:                 26
% 3.02/1.03  sim_bw_subsumption_res:                 0
% 3.02/1.03  sim_tautology_del:                      2
% 3.02/1.03  sim_eq_tautology_del:                   1
% 3.02/1.03  sim_eq_res_simp:                        4
% 3.02/1.03  sim_fw_demodulated:                     0
% 3.02/1.03  sim_bw_demodulated:                     16
% 3.02/1.03  sim_light_normalised:                   36
% 3.02/1.03  sim_joinable_taut:                      0
% 3.02/1.03  sim_joinable_simp:                      0
% 3.02/1.03  sim_ac_normalised:                      0
% 3.02/1.03  sim_smt_subsumption:                    0
% 3.02/1.03  
%------------------------------------------------------------------------------
