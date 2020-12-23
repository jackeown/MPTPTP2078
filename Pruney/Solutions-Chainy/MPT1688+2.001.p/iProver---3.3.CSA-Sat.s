%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:19 EST 2020

% Result     : CounterSatisfiable 0.86s
% Output     : Saturation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 704 expanded)
%              Number of clauses        :   88 ( 229 expanded)
%              Number of leaves         :   11 ( 143 expanded)
%              Depth                    :   15
%              Number of atoms          :  380 (4061 expanded)
%              Number of equality atoms :  158 ( 732 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))
     => k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( k2_funct_1(X2) = X3
                     => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ~ v2_struct_0(X0)
       => ! [X1] :
            ( ~ v2_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_1(X2) )
       => ( v23_waybel_0(X2,X0,X1)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_1(X3) )
             => ( k2_funct_1(X2) = X3
               => v23_waybel_0(X3,X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ v23_waybel_0(X3,X1,X0)
          & k2_funct_1(X2) = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_1(X3) )
      & v23_waybel_0(X2,X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ v23_waybel_0(X3,X1,X0)
          & k2_funct_1(X2) = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_1(X3) )
      & v23_waybel_0(X2,X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v23_waybel_0(X3,X1,X0)
          & k2_funct_1(X2) = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_1(X3) )
     => ( ~ v23_waybel_0(sK5,X1,X0)
        & k2_funct_1(X2) = sK5
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ v23_waybel_0(X3,X1,X0)
            & k2_funct_1(X2) = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_1(X3) )
        & v23_waybel_0(X2,X0,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ v23_waybel_0(X3,sK3,sK2)
          & k2_funct_1(sK4) = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
          & v1_funct_1(X3) )
      & v23_waybel_0(sK4,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v23_waybel_0(sK5,sK3,sK2)
    & k2_funct_1(sK4) = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_1(sK5)
    & v23_waybel_0(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f25,f24])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    k2_funct_1(sK4) = sK5 ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ~ v23_waybel_0(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    v23_waybel_0(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_100,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_298,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_299,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4))) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_777,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4))) ),
    inference(subtyping,[status(esa)],[c_299])).

cnf(c_1095,plain,
    ( k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4)))
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_848,plain,
    ( k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4)))
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_797,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1200,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_145,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_146,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_785,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_146])).

cnf(c_1201,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_1202,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1201])).

cnf(c_1431,plain,
    ( k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4)))
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1095,c_848,c_1200,c_1202])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_245,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_246,plain,
    ( ~ v1_relat_1(sK5)
    | v2_funct_1(sK5)
    | k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5))) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_781,plain,
    ( ~ v1_relat_1(sK5)
    | v2_funct_1(sK5)
    | k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5))) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_1090,plain,
    ( k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5)))
    | v1_relat_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_839,plain,
    ( k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5)))
    | v1_relat_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_1204,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_133,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_134,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_786,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_1205,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1206,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_1383,plain,
    ( k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5)))
    | v2_funct_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_839,c_1204,c_1206])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_286,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_287,plain,
    ( ~ v1_relat_1(sK4)
    | k3_xboole_0(k10_relat_1(sK4,X0),k10_relat_1(sK4,X1)) = k10_relat_1(sK4,k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_778,plain,
    ( ~ v1_relat_1(sK4)
    | k3_xboole_0(k10_relat_1(sK4,X0_47),k10_relat_1(sK4,X1_47)) = k10_relat_1(sK4,k3_xboole_0(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_1094,plain,
    ( k3_xboole_0(k10_relat_1(sK4,X0_47),k10_relat_1(sK4,X1_47)) = k10_relat_1(sK4,k3_xboole_0(X0_47,X1_47))
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_1378,plain,
    ( k3_xboole_0(k10_relat_1(sK4,X0_47),k10_relat_1(sK4,X1_47)) = k10_relat_1(sK4,k3_xboole_0(X0_47,X1_47)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_778,c_1200,c_1201])).

cnf(c_233,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_234,plain,
    ( ~ v1_relat_1(sK5)
    | k3_xboole_0(k10_relat_1(sK5,X0),k10_relat_1(sK5,X1)) = k10_relat_1(sK5,k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_782,plain,
    ( ~ v1_relat_1(sK5)
    | k3_xboole_0(k10_relat_1(sK5,X0_47),k10_relat_1(sK5,X1_47)) = k10_relat_1(sK5,k3_xboole_0(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_234])).

cnf(c_1089,plain,
    ( k3_xboole_0(k10_relat_1(sK5,X0_47),k10_relat_1(sK5,X1_47)) = k10_relat_1(sK5,k3_xboole_0(X0_47,X1_47))
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_1331,plain,
    ( k3_xboole_0(k10_relat_1(sK5,X0_47),k10_relat_1(sK5,X1_47)) = k10_relat_1(sK5,k3_xboole_0(X0_47,X1_47)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1089,c_782,c_1204,c_1205])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_205,plain,
    ( ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_206,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v2_funct_1(sK5)
    | k2_funct_1(k2_funct_1(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_784,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v2_funct_1(sK5)
    | k2_funct_1(k2_funct_1(sK5)) = sK5 ),
    inference(subtyping,[status(esa)],[c_206])).

cnf(c_1086,plain,
    ( k2_funct_1(k2_funct_1(sK5)) = sK5
    | v1_relat_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_831,plain,
    ( k2_funct_1(k2_funct_1(sK5)) = sK5
    | v1_relat_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_1324,plain,
    ( k2_funct_1(k2_funct_1(sK5)) = sK5
    | v2_funct_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1086,c_831,c_1204,c_1206])).

cnf(c_1085,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_1282,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_1200,c_1202])).

cnf(c_1084,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_1276,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_1204,c_1206])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_271,plain,
    ( ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_272,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_779,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_793,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_779])).

cnf(c_1092,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_841,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_1245,plain,
    ( v2_funct_1(sK4) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1092,c_841,c_1200,c_1202])).

cnf(c_218,plain,
    ( ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_219,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v2_funct_1(sK5)
    | k9_relat_1(k2_funct_1(sK5),X0) = k10_relat_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_783,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v2_funct_1(sK5)
    | k9_relat_1(k2_funct_1(sK5),X0_47) = k10_relat_1(sK5,X0_47) ),
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_791,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v2_funct_1(sK5)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_783])).

cnf(c_1087,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_832,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_1238,plain,
    ( v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1087,c_832,c_1204,c_1206])).

cnf(c_258,plain,
    ( ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_259,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_780,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_1091,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_6,negated_conjecture,
    ( k2_funct_1(sK4) = sK5 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_788,negated_conjecture,
    ( k2_funct_1(sK4) = sK5 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1137,plain,
    ( k2_funct_1(sK5) = sK4
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1091,c_788])).

cnf(c_1221,plain,
    ( k2_funct_1(sK5) = sK4
    | v2_funct_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1137,c_1200,c_1202])).

cnf(c_792,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0_47) = k10_relat_1(sK4,X0_47)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_779])).

cnf(c_1093,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0_47) = k10_relat_1(sK4,X0_47)
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_1106,plain,
    ( k10_relat_1(sK4,X0_47) = k9_relat_1(sK5,X0_47)
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1093,c_788])).

cnf(c_790,plain,
    ( k9_relat_1(k2_funct_1(sK5),X0_47) = k10_relat_1(sK5,X0_47)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_783])).

cnf(c_1088,plain,
    ( k9_relat_1(k2_funct_1(sK5),X0_47) = k10_relat_1(sK5,X0_47)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_5,negated_conjecture,
    ( ~ v23_waybel_0(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_789,negated_conjecture,
    ( ~ v23_waybel_0(sK5,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1082,plain,
    ( v23_waybel_0(sK5,sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_9,negated_conjecture,
    ( v23_waybel_0(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_787,negated_conjecture,
    ( v23_waybel_0(sK4,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1083,plain,
    ( v23_waybel_0(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.86/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.86/1.00  
% 0.86/1.00  ------  iProver source info
% 0.86/1.00  
% 0.86/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.86/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.86/1.00  git: non_committed_changes: false
% 0.86/1.00  git: last_make_outside_of_git: false
% 0.86/1.00  
% 0.86/1.00  ------ 
% 0.86/1.00  
% 0.86/1.00  ------ Input Options
% 0.86/1.00  
% 0.86/1.00  --out_options                           all
% 0.86/1.00  --tptp_safe_out                         true
% 0.86/1.00  --problem_path                          ""
% 0.86/1.00  --include_path                          ""
% 0.86/1.00  --clausifier                            res/vclausify_rel
% 0.86/1.00  --clausifier_options                    --mode clausify
% 0.86/1.00  --stdin                                 false
% 0.86/1.00  --stats_out                             all
% 0.86/1.00  
% 0.86/1.00  ------ General Options
% 0.86/1.00  
% 0.86/1.00  --fof                                   false
% 0.86/1.00  --time_out_real                         305.
% 0.86/1.00  --time_out_virtual                      -1.
% 0.86/1.00  --symbol_type_check                     false
% 0.86/1.00  --clausify_out                          false
% 0.86/1.00  --sig_cnt_out                           false
% 0.86/1.00  --trig_cnt_out                          false
% 0.86/1.00  --trig_cnt_out_tolerance                1.
% 0.86/1.00  --trig_cnt_out_sk_spl                   false
% 0.86/1.00  --abstr_cl_out                          false
% 0.86/1.00  
% 0.86/1.00  ------ Global Options
% 0.86/1.00  
% 0.86/1.00  --schedule                              default
% 0.86/1.00  --add_important_lit                     false
% 0.86/1.00  --prop_solver_per_cl                    1000
% 0.86/1.00  --min_unsat_core                        false
% 0.86/1.00  --soft_assumptions                      false
% 0.86/1.00  --soft_lemma_size                       3
% 0.86/1.00  --prop_impl_unit_size                   0
% 0.86/1.00  --prop_impl_unit                        []
% 0.86/1.00  --share_sel_clauses                     true
% 0.86/1.00  --reset_solvers                         false
% 0.86/1.00  --bc_imp_inh                            [conj_cone]
% 0.86/1.00  --conj_cone_tolerance                   3.
% 0.86/1.00  --extra_neg_conj                        none
% 0.86/1.00  --large_theory_mode                     true
% 0.86/1.00  --prolific_symb_bound                   200
% 0.86/1.00  --lt_threshold                          2000
% 0.86/1.00  --clause_weak_htbl                      true
% 0.86/1.00  --gc_record_bc_elim                     false
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing Options
% 0.86/1.00  
% 0.86/1.00  --preprocessing_flag                    true
% 0.86/1.00  --time_out_prep_mult                    0.1
% 0.86/1.00  --splitting_mode                        input
% 0.86/1.00  --splitting_grd                         true
% 0.86/1.00  --splitting_cvd                         false
% 0.86/1.00  --splitting_cvd_svl                     false
% 0.86/1.00  --splitting_nvd                         32
% 0.86/1.00  --sub_typing                            true
% 0.86/1.00  --prep_gs_sim                           true
% 0.86/1.00  --prep_unflatten                        true
% 0.86/1.00  --prep_res_sim                          true
% 0.86/1.00  --prep_upred                            true
% 0.86/1.00  --prep_sem_filter                       exhaustive
% 0.86/1.00  --prep_sem_filter_out                   false
% 0.86/1.00  --pred_elim                             true
% 0.86/1.00  --res_sim_input                         true
% 0.86/1.00  --eq_ax_congr_red                       true
% 0.86/1.00  --pure_diseq_elim                       true
% 0.86/1.00  --brand_transform                       false
% 0.86/1.00  --non_eq_to_eq                          false
% 0.86/1.00  --prep_def_merge                        true
% 0.86/1.00  --prep_def_merge_prop_impl              false
% 0.86/1.00  --prep_def_merge_mbd                    true
% 0.86/1.00  --prep_def_merge_tr_red                 false
% 0.86/1.00  --prep_def_merge_tr_cl                  false
% 0.86/1.00  --smt_preprocessing                     true
% 0.86/1.00  --smt_ac_axioms                         fast
% 0.86/1.00  --preprocessed_out                      false
% 0.86/1.00  --preprocessed_stats                    false
% 0.86/1.00  
% 0.86/1.00  ------ Abstraction refinement Options
% 0.86/1.00  
% 0.86/1.00  --abstr_ref                             []
% 0.86/1.00  --abstr_ref_prep                        false
% 0.86/1.00  --abstr_ref_until_sat                   false
% 0.86/1.00  --abstr_ref_sig_restrict                funpre
% 0.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.00  --abstr_ref_under                       []
% 0.86/1.00  
% 0.86/1.00  ------ SAT Options
% 0.86/1.00  
% 0.86/1.00  --sat_mode                              false
% 0.86/1.00  --sat_fm_restart_options                ""
% 0.86/1.00  --sat_gr_def                            false
% 0.86/1.00  --sat_epr_types                         true
% 0.86/1.00  --sat_non_cyclic_types                  false
% 0.86/1.00  --sat_finite_models                     false
% 0.86/1.00  --sat_fm_lemmas                         false
% 0.86/1.00  --sat_fm_prep                           false
% 0.86/1.00  --sat_fm_uc_incr                        true
% 0.86/1.00  --sat_out_model                         small
% 0.86/1.00  --sat_out_clauses                       false
% 0.86/1.00  
% 0.86/1.00  ------ QBF Options
% 0.86/1.00  
% 0.86/1.00  --qbf_mode                              false
% 0.86/1.00  --qbf_elim_univ                         false
% 0.86/1.00  --qbf_dom_inst                          none
% 0.86/1.00  --qbf_dom_pre_inst                      false
% 0.86/1.00  --qbf_sk_in                             false
% 0.86/1.00  --qbf_pred_elim                         true
% 0.86/1.00  --qbf_split                             512
% 0.86/1.00  
% 0.86/1.00  ------ BMC1 Options
% 0.86/1.00  
% 0.86/1.00  --bmc1_incremental                      false
% 0.86/1.00  --bmc1_axioms                           reachable_all
% 0.86/1.00  --bmc1_min_bound                        0
% 0.86/1.00  --bmc1_max_bound                        -1
% 0.86/1.00  --bmc1_max_bound_default                -1
% 0.86/1.00  --bmc1_symbol_reachability              true
% 0.86/1.00  --bmc1_property_lemmas                  false
% 0.86/1.00  --bmc1_k_induction                      false
% 0.86/1.00  --bmc1_non_equiv_states                 false
% 0.86/1.00  --bmc1_deadlock                         false
% 0.86/1.00  --bmc1_ucm                              false
% 0.86/1.00  --bmc1_add_unsat_core                   none
% 0.86/1.00  --bmc1_unsat_core_children              false
% 0.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.00  --bmc1_out_stat                         full
% 0.86/1.00  --bmc1_ground_init                      false
% 0.86/1.00  --bmc1_pre_inst_next_state              false
% 0.86/1.00  --bmc1_pre_inst_state                   false
% 0.86/1.00  --bmc1_pre_inst_reach_state             false
% 0.86/1.00  --bmc1_out_unsat_core                   false
% 0.86/1.00  --bmc1_aig_witness_out                  false
% 0.86/1.00  --bmc1_verbose                          false
% 0.86/1.00  --bmc1_dump_clauses_tptp                false
% 0.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.00  --bmc1_dump_file                        -
% 0.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.00  --bmc1_ucm_extend_mode                  1
% 0.86/1.00  --bmc1_ucm_init_mode                    2
% 0.86/1.00  --bmc1_ucm_cone_mode                    none
% 0.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.00  --bmc1_ucm_relax_model                  4
% 0.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.00  --bmc1_ucm_layered_model                none
% 0.86/1.00  --bmc1_ucm_max_lemma_size               10
% 0.86/1.00  
% 0.86/1.00  ------ AIG Options
% 0.86/1.00  
% 0.86/1.00  --aig_mode                              false
% 0.86/1.00  
% 0.86/1.00  ------ Instantiation Options
% 0.86/1.00  
% 0.86/1.00  --instantiation_flag                    true
% 0.86/1.00  --inst_sos_flag                         false
% 0.86/1.00  --inst_sos_phase                        true
% 0.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel_side                     num_symb
% 0.86/1.00  --inst_solver_per_active                1400
% 0.86/1.00  --inst_solver_calls_frac                1.
% 0.86/1.00  --inst_passive_queue_type               priority_queues
% 0.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.00  --inst_passive_queues_freq              [25;2]
% 0.86/1.00  --inst_dismatching                      true
% 0.86/1.00  --inst_eager_unprocessed_to_passive     true
% 0.86/1.00  --inst_prop_sim_given                   true
% 0.86/1.00  --inst_prop_sim_new                     false
% 0.86/1.00  --inst_subs_new                         false
% 0.86/1.00  --inst_eq_res_simp                      false
% 0.86/1.00  --inst_subs_given                       false
% 0.86/1.00  --inst_orphan_elimination               true
% 0.86/1.00  --inst_learning_loop_flag               true
% 0.86/1.00  --inst_learning_start                   3000
% 0.86/1.00  --inst_learning_factor                  2
% 0.86/1.00  --inst_start_prop_sim_after_learn       3
% 0.86/1.00  --inst_sel_renew                        solver
% 0.86/1.00  --inst_lit_activity_flag                true
% 0.86/1.00  --inst_restr_to_given                   false
% 0.86/1.00  --inst_activity_threshold               500
% 0.86/1.00  --inst_out_proof                        true
% 0.86/1.00  
% 0.86/1.00  ------ Resolution Options
% 0.86/1.00  
% 0.86/1.00  --resolution_flag                       true
% 0.86/1.00  --res_lit_sel                           adaptive
% 0.86/1.00  --res_lit_sel_side                      none
% 0.86/1.00  --res_ordering                          kbo
% 0.86/1.00  --res_to_prop_solver                    active
% 0.86/1.00  --res_prop_simpl_new                    false
% 0.86/1.00  --res_prop_simpl_given                  true
% 0.86/1.00  --res_passive_queue_type                priority_queues
% 0.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.00  --res_passive_queues_freq               [15;5]
% 0.86/1.00  --res_forward_subs                      full
% 0.86/1.00  --res_backward_subs                     full
% 0.86/1.00  --res_forward_subs_resolution           true
% 0.86/1.00  --res_backward_subs_resolution          true
% 0.86/1.00  --res_orphan_elimination                true
% 0.86/1.00  --res_time_limit                        2.
% 0.86/1.00  --res_out_proof                         true
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Options
% 0.86/1.00  
% 0.86/1.00  --superposition_flag                    true
% 0.86/1.00  --sup_passive_queue_type                priority_queues
% 0.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.00  --demod_completeness_check              fast
% 0.86/1.00  --demod_use_ground                      true
% 0.86/1.00  --sup_to_prop_solver                    passive
% 0.86/1.00  --sup_prop_simpl_new                    true
% 0.86/1.00  --sup_prop_simpl_given                  true
% 0.86/1.00  --sup_fun_splitting                     false
% 0.86/1.00  --sup_smt_interval                      50000
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Simplification Setup
% 0.86/1.00  
% 0.86/1.00  --sup_indices_passive                   []
% 0.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_full_bw                           [BwDemod]
% 0.86/1.00  --sup_immed_triv                        [TrivRules]
% 0.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_immed_bw_main                     []
% 0.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  
% 0.86/1.00  ------ Combination Options
% 0.86/1.00  
% 0.86/1.00  --comb_res_mult                         3
% 0.86/1.00  --comb_sup_mult                         2
% 0.86/1.00  --comb_inst_mult                        10
% 0.86/1.00  
% 0.86/1.00  ------ Debug Options
% 0.86/1.00  
% 0.86/1.00  --dbg_backtrace                         false
% 0.86/1.00  --dbg_dump_prop_clauses                 false
% 0.86/1.00  --dbg_dump_prop_clauses_file            -
% 0.86/1.00  --dbg_out_stat                          false
% 0.86/1.00  ------ Parsing...
% 0.86/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.86/1.00  ------ Proving...
% 0.86/1.00  ------ Problem Properties 
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  clauses                                 15
% 0.86/1.00  conjectures                             3
% 0.86/1.00  EPR                                     4
% 0.86/1.00  Horn                                    15
% 0.86/1.00  unary                                   3
% 0.86/1.00  binary                                  6
% 0.86/1.00  lits                                    33
% 0.86/1.00  lits eq                                 11
% 0.86/1.00  fd_pure                                 0
% 0.86/1.00  fd_pseudo                               0
% 0.86/1.00  fd_cond                                 0
% 0.86/1.00  fd_pseudo_cond                          0
% 0.86/1.00  AC symbols                              0
% 0.86/1.00  
% 0.86/1.00  ------ Schedule dynamic 5 is on 
% 0.86/1.00  
% 0.86/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  ------ 
% 0.86/1.00  Current options:
% 0.86/1.00  ------ 
% 0.86/1.00  
% 0.86/1.00  ------ Input Options
% 0.86/1.00  
% 0.86/1.00  --out_options                           all
% 0.86/1.00  --tptp_safe_out                         true
% 0.86/1.00  --problem_path                          ""
% 0.86/1.00  --include_path                          ""
% 0.86/1.00  --clausifier                            res/vclausify_rel
% 0.86/1.00  --clausifier_options                    --mode clausify
% 0.86/1.00  --stdin                                 false
% 0.86/1.00  --stats_out                             all
% 0.86/1.00  
% 0.86/1.00  ------ General Options
% 0.86/1.00  
% 0.86/1.00  --fof                                   false
% 0.86/1.00  --time_out_real                         305.
% 0.86/1.00  --time_out_virtual                      -1.
% 0.86/1.00  --symbol_type_check                     false
% 0.86/1.00  --clausify_out                          false
% 0.86/1.00  --sig_cnt_out                           false
% 0.86/1.00  --trig_cnt_out                          false
% 0.86/1.00  --trig_cnt_out_tolerance                1.
% 0.86/1.00  --trig_cnt_out_sk_spl                   false
% 0.86/1.00  --abstr_cl_out                          false
% 0.86/1.00  
% 0.86/1.00  ------ Global Options
% 0.86/1.00  
% 0.86/1.00  --schedule                              default
% 0.86/1.00  --add_important_lit                     false
% 0.86/1.00  --prop_solver_per_cl                    1000
% 0.86/1.00  --min_unsat_core                        false
% 0.86/1.00  --soft_assumptions                      false
% 0.86/1.00  --soft_lemma_size                       3
% 0.86/1.00  --prop_impl_unit_size                   0
% 0.86/1.00  --prop_impl_unit                        []
% 0.86/1.00  --share_sel_clauses                     true
% 0.86/1.00  --reset_solvers                         false
% 0.86/1.00  --bc_imp_inh                            [conj_cone]
% 0.86/1.00  --conj_cone_tolerance                   3.
% 0.86/1.00  --extra_neg_conj                        none
% 0.86/1.00  --large_theory_mode                     true
% 0.86/1.00  --prolific_symb_bound                   200
% 0.86/1.00  --lt_threshold                          2000
% 0.86/1.00  --clause_weak_htbl                      true
% 0.86/1.00  --gc_record_bc_elim                     false
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing Options
% 0.86/1.00  
% 0.86/1.00  --preprocessing_flag                    true
% 0.86/1.00  --time_out_prep_mult                    0.1
% 0.86/1.00  --splitting_mode                        input
% 0.86/1.00  --splitting_grd                         true
% 0.86/1.00  --splitting_cvd                         false
% 0.86/1.00  --splitting_cvd_svl                     false
% 0.86/1.00  --splitting_nvd                         32
% 0.86/1.00  --sub_typing                            true
% 0.86/1.00  --prep_gs_sim                           true
% 0.86/1.00  --prep_unflatten                        true
% 0.86/1.00  --prep_res_sim                          true
% 0.86/1.00  --prep_upred                            true
% 0.86/1.00  --prep_sem_filter                       exhaustive
% 0.86/1.00  --prep_sem_filter_out                   false
% 0.86/1.00  --pred_elim                             true
% 0.86/1.00  --res_sim_input                         true
% 0.86/1.00  --eq_ax_congr_red                       true
% 0.86/1.00  --pure_diseq_elim                       true
% 0.86/1.00  --brand_transform                       false
% 0.86/1.00  --non_eq_to_eq                          false
% 0.86/1.00  --prep_def_merge                        true
% 0.86/1.00  --prep_def_merge_prop_impl              false
% 0.86/1.00  --prep_def_merge_mbd                    true
% 0.86/1.00  --prep_def_merge_tr_red                 false
% 0.86/1.00  --prep_def_merge_tr_cl                  false
% 0.86/1.00  --smt_preprocessing                     true
% 0.86/1.00  --smt_ac_axioms                         fast
% 0.86/1.00  --preprocessed_out                      false
% 0.86/1.00  --preprocessed_stats                    false
% 0.86/1.00  
% 0.86/1.00  ------ Abstraction refinement Options
% 0.86/1.00  
% 0.86/1.00  --abstr_ref                             []
% 0.86/1.00  --abstr_ref_prep                        false
% 0.86/1.00  --abstr_ref_until_sat                   false
% 0.86/1.00  --abstr_ref_sig_restrict                funpre
% 0.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.00  --abstr_ref_under                       []
% 0.86/1.00  
% 0.86/1.00  ------ SAT Options
% 0.86/1.00  
% 0.86/1.00  --sat_mode                              false
% 0.86/1.00  --sat_fm_restart_options                ""
% 0.86/1.00  --sat_gr_def                            false
% 0.86/1.00  --sat_epr_types                         true
% 0.86/1.00  --sat_non_cyclic_types                  false
% 0.86/1.00  --sat_finite_models                     false
% 0.86/1.00  --sat_fm_lemmas                         false
% 0.86/1.00  --sat_fm_prep                           false
% 0.86/1.00  --sat_fm_uc_incr                        true
% 0.86/1.00  --sat_out_model                         small
% 0.86/1.00  --sat_out_clauses                       false
% 0.86/1.00  
% 0.86/1.00  ------ QBF Options
% 0.86/1.00  
% 0.86/1.00  --qbf_mode                              false
% 0.86/1.00  --qbf_elim_univ                         false
% 0.86/1.00  --qbf_dom_inst                          none
% 0.86/1.00  --qbf_dom_pre_inst                      false
% 0.86/1.00  --qbf_sk_in                             false
% 0.86/1.00  --qbf_pred_elim                         true
% 0.86/1.00  --qbf_split                             512
% 0.86/1.00  
% 0.86/1.00  ------ BMC1 Options
% 0.86/1.00  
% 0.86/1.00  --bmc1_incremental                      false
% 0.86/1.00  --bmc1_axioms                           reachable_all
% 0.86/1.00  --bmc1_min_bound                        0
% 0.86/1.00  --bmc1_max_bound                        -1
% 0.86/1.00  --bmc1_max_bound_default                -1
% 0.86/1.00  --bmc1_symbol_reachability              true
% 0.86/1.00  --bmc1_property_lemmas                  false
% 0.86/1.00  --bmc1_k_induction                      false
% 0.86/1.00  --bmc1_non_equiv_states                 false
% 0.86/1.00  --bmc1_deadlock                         false
% 0.86/1.00  --bmc1_ucm                              false
% 0.86/1.00  --bmc1_add_unsat_core                   none
% 0.86/1.00  --bmc1_unsat_core_children              false
% 0.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.00  --bmc1_out_stat                         full
% 0.86/1.00  --bmc1_ground_init                      false
% 0.86/1.00  --bmc1_pre_inst_next_state              false
% 0.86/1.00  --bmc1_pre_inst_state                   false
% 0.86/1.00  --bmc1_pre_inst_reach_state             false
% 0.86/1.00  --bmc1_out_unsat_core                   false
% 0.86/1.00  --bmc1_aig_witness_out                  false
% 0.86/1.00  --bmc1_verbose                          false
% 0.86/1.00  --bmc1_dump_clauses_tptp                false
% 0.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.00  --bmc1_dump_file                        -
% 0.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.00  --bmc1_ucm_extend_mode                  1
% 0.86/1.00  --bmc1_ucm_init_mode                    2
% 0.86/1.00  --bmc1_ucm_cone_mode                    none
% 0.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.00  --bmc1_ucm_relax_model                  4
% 0.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.00  --bmc1_ucm_layered_model                none
% 0.86/1.00  --bmc1_ucm_max_lemma_size               10
% 0.86/1.00  
% 0.86/1.00  ------ AIG Options
% 0.86/1.00  
% 0.86/1.00  --aig_mode                              false
% 0.86/1.00  
% 0.86/1.00  ------ Instantiation Options
% 0.86/1.00  
% 0.86/1.00  --instantiation_flag                    true
% 0.86/1.00  --inst_sos_flag                         false
% 0.86/1.00  --inst_sos_phase                        true
% 0.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel_side                     none
% 0.86/1.00  --inst_solver_per_active                1400
% 0.86/1.00  --inst_solver_calls_frac                1.
% 0.86/1.00  --inst_passive_queue_type               priority_queues
% 0.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.00  --inst_passive_queues_freq              [25;2]
% 0.86/1.00  --inst_dismatching                      true
% 0.86/1.00  --inst_eager_unprocessed_to_passive     true
% 0.86/1.00  --inst_prop_sim_given                   true
% 0.86/1.00  --inst_prop_sim_new                     false
% 0.86/1.00  --inst_subs_new                         false
% 0.86/1.00  --inst_eq_res_simp                      false
% 0.86/1.00  --inst_subs_given                       false
% 0.86/1.00  --inst_orphan_elimination               true
% 0.86/1.00  --inst_learning_loop_flag               true
% 0.86/1.00  --inst_learning_start                   3000
% 0.86/1.00  --inst_learning_factor                  2
% 0.86/1.00  --inst_start_prop_sim_after_learn       3
% 0.86/1.00  --inst_sel_renew                        solver
% 0.86/1.00  --inst_lit_activity_flag                true
% 0.86/1.00  --inst_restr_to_given                   false
% 0.86/1.00  --inst_activity_threshold               500
% 0.86/1.00  --inst_out_proof                        true
% 0.86/1.00  
% 0.86/1.00  ------ Resolution Options
% 0.86/1.00  
% 0.86/1.00  --resolution_flag                       false
% 0.86/1.00  --res_lit_sel                           adaptive
% 0.86/1.00  --res_lit_sel_side                      none
% 0.86/1.00  --res_ordering                          kbo
% 0.86/1.00  --res_to_prop_solver                    active
% 0.86/1.00  --res_prop_simpl_new                    false
% 0.86/1.00  --res_prop_simpl_given                  true
% 0.86/1.00  --res_passive_queue_type                priority_queues
% 0.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.00  --res_passive_queues_freq               [15;5]
% 0.86/1.00  --res_forward_subs                      full
% 0.86/1.00  --res_backward_subs                     full
% 0.86/1.00  --res_forward_subs_resolution           true
% 0.86/1.00  --res_backward_subs_resolution          true
% 0.86/1.00  --res_orphan_elimination                true
% 0.86/1.00  --res_time_limit                        2.
% 0.86/1.00  --res_out_proof                         true
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Options
% 0.86/1.00  
% 0.86/1.00  --superposition_flag                    true
% 0.86/1.00  --sup_passive_queue_type                priority_queues
% 0.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.00  --demod_completeness_check              fast
% 0.86/1.00  --demod_use_ground                      true
% 0.86/1.00  --sup_to_prop_solver                    passive
% 0.86/1.00  --sup_prop_simpl_new                    true
% 0.86/1.00  --sup_prop_simpl_given                  true
% 0.86/1.00  --sup_fun_splitting                     false
% 0.86/1.00  --sup_smt_interval                      50000
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Simplification Setup
% 0.86/1.00  
% 0.86/1.00  --sup_indices_passive                   []
% 0.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_full_bw                           [BwDemod]
% 0.86/1.00  --sup_immed_triv                        [TrivRules]
% 0.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_immed_bw_main                     []
% 0.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  
% 0.86/1.00  ------ Combination Options
% 0.86/1.00  
% 0.86/1.00  --comb_res_mult                         3
% 0.86/1.00  --comb_sup_mult                         2
% 0.86/1.00  --comb_inst_mult                        10
% 0.86/1.00  
% 0.86/1.00  ------ Debug Options
% 0.86/1.00  
% 0.86/1.00  --dbg_backtrace                         false
% 0.86/1.00  --dbg_dump_prop_clauses                 false
% 0.86/1.00  --dbg_dump_prop_clauses_file            -
% 0.86/1.00  --dbg_out_stat                          false
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  ------ Proving...
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  % SZS output start Saturation for theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  fof(f1,axiom,(
% 0.86/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2)) => v2_funct_1(X0)))),
% 0.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f11,plain,(
% 0.86/1.00    ! [X0] : ((v2_funct_1(X0) | ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.86/1.00    inference(ennf_transformation,[],[f1])).
% 0.86/1.00  
% 0.86/1.00  fof(f12,plain,(
% 0.86/1.00    ! [X0] : (v2_funct_1(X0) | ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.86/1.00    inference(flattening,[],[f11])).
% 0.86/1.00  
% 0.86/1.00  fof(f22,plain,(
% 0.86/1.00    ! [X0] : (? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2)) => k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0))))),
% 0.86/1.00    introduced(choice_axiom,[])).
% 0.86/1.00  
% 0.86/1.00  fof(f23,plain,(
% 0.86/1.00    ! [X0] : (v2_funct_1(X0) | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22])).
% 0.86/1.00  
% 0.86/1.00  fof(f27,plain,(
% 0.86/1.00    ( ! [X0] : (v2_funct_1(X0) | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f23])).
% 0.86/1.00  
% 0.86/1.00  fof(f6,conjecture,(
% 0.86/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (k2_funct_1(X2) = X3 => v23_waybel_0(X3,X1,X0)))))))),
% 0.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f7,negated_conjecture,(
% 0.86/1.00    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (k2_funct_1(X2) = X3 => v23_waybel_0(X3,X1,X0)))))))),
% 0.86/1.00    inference(negated_conjecture,[],[f6])).
% 0.86/1.00  
% 0.86/1.00  fof(f8,plain,(
% 0.86/1.00    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3)) => (k2_funct_1(X2) = X3 => v23_waybel_0(X3,X1,X0)))))))),
% 0.86/1.00    inference(pure_predicate_removal,[],[f7])).
% 0.86/1.00  
% 0.86/1.00  fof(f9,plain,(
% 0.86/1.00    ~! [X0] : (~v2_struct_0(X0) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3)) => (k2_funct_1(X2) = X3 => v23_waybel_0(X3,X1,X0)))))))),
% 0.86/1.00    inference(pure_predicate_removal,[],[f8])).
% 0.86/1.00  
% 0.86/1.00  fof(f10,plain,(
% 0.86/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3)) => (k2_funct_1(X2) = X3 => v23_waybel_0(X3,X1,X0)))))),
% 0.86/1.00    inference(pure_predicate_removal,[],[f9])).
% 0.86/1.00  
% 0.86/1.00  fof(f20,plain,(
% 0.86/1.00    ? [X0,X1,X2] : ((? [X3] : ((~v23_waybel_0(X3,X1,X0) & k2_funct_1(X2) = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3))) & v23_waybel_0(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_1(X2)))),
% 0.86/1.00    inference(ennf_transformation,[],[f10])).
% 0.86/1.00  
% 0.86/1.00  fof(f21,plain,(
% 0.86/1.00    ? [X0,X1,X2] : (? [X3] : (~v23_waybel_0(X3,X1,X0) & k2_funct_1(X2) = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3)) & v23_waybel_0(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_1(X2))),
% 0.86/1.00    inference(flattening,[],[f20])).
% 0.86/1.00  
% 0.86/1.00  fof(f25,plain,(
% 0.86/1.00    ( ! [X2,X0,X1] : (? [X3] : (~v23_waybel_0(X3,X1,X0) & k2_funct_1(X2) = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3)) => (~v23_waybel_0(sK5,X1,X0) & k2_funct_1(X2) = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(sK5))) )),
% 0.86/1.00    introduced(choice_axiom,[])).
% 0.86/1.00  
% 0.86/1.00  fof(f24,plain,(
% 0.86/1.00    ? [X0,X1,X2] : (? [X3] : (~v23_waybel_0(X3,X1,X0) & k2_funct_1(X2) = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(X3)) & v23_waybel_0(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_1(X2)) => (? [X3] : (~v23_waybel_0(X3,sK3,sK2) & k2_funct_1(sK4) = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_1(X3)) & v23_waybel_0(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_1(sK4))),
% 0.86/1.00    introduced(choice_axiom,[])).
% 0.86/1.00  
% 0.86/1.00  fof(f26,plain,(
% 0.86/1.00    (~v23_waybel_0(sK5,sK3,sK2) & k2_funct_1(sK4) = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_1(sK5)) & v23_waybel_0(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_1(sK4)),
% 0.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f25,f24])).
% 0.86/1.00  
% 0.86/1.00  fof(f32,plain,(
% 0.86/1.00    v1_funct_1(sK4)),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  fof(f5,axiom,(
% 0.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f19,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.86/1.00    inference(ennf_transformation,[],[f5])).
% 0.86/1.00  
% 0.86/1.00  fof(f31,plain,(
% 0.86/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.86/1.00    inference(cnf_transformation,[],[f19])).
% 0.86/1.00  
% 0.86/1.00  fof(f33,plain,(
% 0.86/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  fof(f35,plain,(
% 0.86/1.00    v1_funct_1(sK5)),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  fof(f36,plain,(
% 0.86/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  fof(f2,axiom,(
% 0.86/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f13,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.86/1.00    inference(ennf_transformation,[],[f2])).
% 0.86/1.00  
% 0.86/1.00  fof(f14,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.86/1.00    inference(flattening,[],[f13])).
% 0.86/1.00  
% 0.86/1.00  fof(f28,plain,(
% 0.86/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f14])).
% 0.86/1.00  
% 0.86/1.00  fof(f4,axiom,(
% 0.86/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f17,plain,(
% 0.86/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.86/1.00    inference(ennf_transformation,[],[f4])).
% 0.86/1.00  
% 0.86/1.00  fof(f18,plain,(
% 0.86/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.86/1.00    inference(flattening,[],[f17])).
% 0.86/1.00  
% 0.86/1.00  fof(f30,plain,(
% 0.86/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f18])).
% 0.86/1.00  
% 0.86/1.00  fof(f3,axiom,(
% 0.86/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 0.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f15,plain,(
% 0.86/1.00    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.86/1.00    inference(ennf_transformation,[],[f3])).
% 0.86/1.00  
% 0.86/1.00  fof(f16,plain,(
% 0.86/1.00    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.86/1.00    inference(flattening,[],[f15])).
% 0.86/1.00  
% 0.86/1.00  fof(f29,plain,(
% 0.86/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f37,plain,(
% 0.86/1.00    k2_funct_1(sK4) = sK5),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  fof(f38,plain,(
% 0.86/1.00    ~v23_waybel_0(sK5,sK3,sK2)),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  fof(f34,plain,(
% 0.86/1.00    v23_waybel_0(sK4,sK2,sK3)),
% 0.86/1.00    inference(cnf_transformation,[],[f26])).
% 0.86/1.00  
% 0.86/1.00  cnf(c_100,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_0,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | v2_funct_1(X0)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0))) ),
% 0.86/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_11,negated_conjecture,
% 0.86/1.00      ( v1_funct_1(sK4) ),
% 0.86/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_298,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | v2_funct_1(X0)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0)))
% 0.86/1.00      | sK4 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_299,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | v2_funct_1(sK4)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4))) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_298]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_777,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | v2_funct_1(sK4)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4))) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_299]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1095,plain,
% 0.86/1.00      ( k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4)))
% 0.86/1.00      | v1_relat_1(sK4) != iProver_top
% 0.86/1.00      | v2_funct_1(sK4) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_848,plain,
% 0.86/1.00      ( k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4)))
% 0.86/1.00      | v1_relat_1(sK4) != iProver_top
% 0.86/1.00      | v2_funct_1(sK4) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_797,plain,( X0_48 = X0_48 ),theory(equality) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1200,plain,
% 0.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_797]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_4,plain,
% 0.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.86/1.00      inference(cnf_transformation,[],[f31]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_10,negated_conjecture,
% 0.86/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 0.86/1.00      inference(cnf_transformation,[],[f33]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_145,plain,
% 0.86/1.00      ( v1_relat_1(X0)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.86/1.00      | sK4 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_146,plain,
% 0.86/1.00      ( v1_relat_1(sK4)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_145]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_785,plain,
% 0.86/1.00      ( v1_relat_1(sK4)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_146]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1201,plain,
% 0.86/1.00      ( v1_relat_1(sK4)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_785]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1202,plain,
% 0.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 0.86/1.00      | v1_relat_1(sK4) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1201]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1431,plain,
% 0.86/1.00      ( k3_xboole_0(k9_relat_1(sK4,sK0(sK4)),k9_relat_1(sK4,sK1(sK4))) != k9_relat_1(sK4,k3_xboole_0(sK0(sK4),sK1(sK4)))
% 0.86/1.00      | v2_funct_1(sK4) = iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1095,c_848,c_1200,c_1202]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_8,negated_conjecture,
% 0.86/1.00      ( v1_funct_1(sK5) ),
% 0.86/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_245,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | v2_funct_1(X0)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(X0,sK0(X0)),k9_relat_1(X0,sK1(X0))) != k9_relat_1(X0,k3_xboole_0(sK0(X0),sK1(X0)))
% 0.86/1.00      | sK5 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_246,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | v2_funct_1(sK5)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5))) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_781,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | v2_funct_1(sK5)
% 0.86/1.00      | k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5))) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_246]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1090,plain,
% 0.86/1.00      ( k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5)))
% 0.86/1.00      | v1_relat_1(sK5) != iProver_top
% 0.86/1.00      | v2_funct_1(sK5) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_839,plain,
% 0.86/1.00      ( k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5)))
% 0.86/1.00      | v1_relat_1(sK5) != iProver_top
% 0.86/1.00      | v2_funct_1(sK5) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1204,plain,
% 0.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_797]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_7,negated_conjecture,
% 0.86/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 0.86/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_133,plain,
% 0.86/1.00      ( v1_relat_1(X0)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.86/1.00      | sK5 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_134,plain,
% 0.86/1.00      ( v1_relat_1(sK5)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_133]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_786,plain,
% 0.86/1.00      ( v1_relat_1(sK5)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_134]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1205,plain,
% 0.86/1.00      ( v1_relat_1(sK5)
% 0.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_786]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1206,plain,
% 0.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 0.86/1.00      | v1_relat_1(sK5) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1205]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1383,plain,
% 0.86/1.00      ( k3_xboole_0(k9_relat_1(sK5,sK0(sK5)),k9_relat_1(sK5,sK1(sK5))) != k9_relat_1(sK5,k3_xboole_0(sK0(sK5),sK1(sK5)))
% 0.86/1.00      | v2_funct_1(sK5) = iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1090,c_839,c_1204,c_1206]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 0.86/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_286,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
% 0.86/1.00      | sK4 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_287,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(sK4,X0),k10_relat_1(sK4,X1)) = k10_relat_1(sK4,k3_xboole_0(X0,X1)) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_778,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(sK4,X0_47),k10_relat_1(sK4,X1_47)) = k10_relat_1(sK4,k3_xboole_0(X0_47,X1_47)) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_287]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1094,plain,
% 0.86/1.00      ( k3_xboole_0(k10_relat_1(sK4,X0_47),k10_relat_1(sK4,X1_47)) = k10_relat_1(sK4,k3_xboole_0(X0_47,X1_47))
% 0.86/1.00      | v1_relat_1(sK4) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1378,plain,
% 0.86/1.00      ( k3_xboole_0(k10_relat_1(sK4,X0_47),k10_relat_1(sK4,X1_47)) = k10_relat_1(sK4,k3_xboole_0(X0_47,X1_47)) ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1094,c_778,c_1200,c_1201]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_233,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
% 0.86/1.00      | sK5 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_234,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(sK5,X0),k10_relat_1(sK5,X1)) = k10_relat_1(sK5,k3_xboole_0(X0,X1)) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_233]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_782,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | k3_xboole_0(k10_relat_1(sK5,X0_47),k10_relat_1(sK5,X1_47)) = k10_relat_1(sK5,k3_xboole_0(X0_47,X1_47)) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_234]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1089,plain,
% 0.86/1.00      ( k3_xboole_0(k10_relat_1(sK5,X0_47),k10_relat_1(sK5,X1_47)) = k10_relat_1(sK5,k3_xboole_0(X0_47,X1_47))
% 0.86/1.00      | v1_relat_1(sK5) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1331,plain,
% 0.86/1.00      ( k3_xboole_0(k10_relat_1(sK5,X0_47),k10_relat_1(sK5,X1_47)) = k10_relat_1(sK5,k3_xboole_0(X0_47,X1_47)) ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1089,c_782,c_1204,c_1205]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_3,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | ~ v2_funct_1(X0)
% 0.86/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 0.86/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_205,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v2_funct_1(X0)
% 0.86/1.00      | k2_funct_1(k2_funct_1(X0)) = X0
% 0.86/1.00      | sK5 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_206,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | ~ v2_funct_1(sK5)
% 0.86/1.00      | k2_funct_1(k2_funct_1(sK5)) = sK5 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_205]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_784,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | ~ v2_funct_1(sK5)
% 0.86/1.00      | k2_funct_1(k2_funct_1(sK5)) = sK5 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_206]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1086,plain,
% 0.86/1.00      ( k2_funct_1(k2_funct_1(sK5)) = sK5
% 0.86/1.00      | v1_relat_1(sK5) != iProver_top
% 0.86/1.00      | v2_funct_1(sK5) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_831,plain,
% 0.86/1.00      ( k2_funct_1(k2_funct_1(sK5)) = sK5
% 0.86/1.00      | v1_relat_1(sK5) != iProver_top
% 0.86/1.00      | v2_funct_1(sK5) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1324,plain,
% 0.86/1.00      ( k2_funct_1(k2_funct_1(sK5)) = sK5 | v2_funct_1(sK5) != iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1086,c_831,c_1204,c_1206]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1085,plain,
% 0.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 0.86/1.00      | v1_relat_1(sK4) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1282,plain,
% 0.86/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1085,c_1200,c_1202]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1084,plain,
% 0.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 0.86/1.00      | v1_relat_1(sK5) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1276,plain,
% 0.86/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1084,c_1204,c_1206]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_2,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | ~ v2_funct_1(X0)
% 0.86/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 0.86/1.00      inference(cnf_transformation,[],[f29]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_271,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v2_funct_1(X0)
% 0.86/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 0.86/1.00      | sK4 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_272,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | ~ v2_funct_1(sK4)
% 0.86/1.00      | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_271]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_779,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | ~ v2_funct_1(sK4)
% 0.86/1.00      | k9_relat_1(k2_funct_1(sK4),X0_47) = k10_relat_1(sK4,X0_47) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_272]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_793,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4) | ~ v2_funct_1(sK4) | sP1_iProver_split ),
% 0.86/1.00      inference(splitting,
% 0.86/1.00                [splitting(split),new_symbols(definition,[])],
% 0.86/1.00                [c_779]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1092,plain,
% 0.86/1.00      ( v1_relat_1(sK4) != iProver_top
% 0.86/1.00      | v2_funct_1(sK4) != iProver_top
% 0.86/1.00      | sP1_iProver_split = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_841,plain,
% 0.86/1.00      ( v1_relat_1(sK4) != iProver_top
% 0.86/1.00      | v2_funct_1(sK4) != iProver_top
% 0.86/1.00      | sP1_iProver_split = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1245,plain,
% 0.86/1.00      ( v2_funct_1(sK4) != iProver_top | sP1_iProver_split = iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1092,c_841,c_1200,c_1202]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_218,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v2_funct_1(X0)
% 0.86/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 0.86/1.00      | sK5 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_219,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | ~ v2_funct_1(sK5)
% 0.86/1.00      | k9_relat_1(k2_funct_1(sK5),X0) = k10_relat_1(sK5,X0) ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_218]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_783,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5)
% 0.86/1.00      | ~ v2_funct_1(sK5)
% 0.86/1.00      | k9_relat_1(k2_funct_1(sK5),X0_47) = k10_relat_1(sK5,X0_47) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_219]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_791,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK5) | ~ v2_funct_1(sK5) | sP0_iProver_split ),
% 0.86/1.00      inference(splitting,
% 0.86/1.00                [splitting(split),new_symbols(definition,[])],
% 0.86/1.00                [c_783]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1087,plain,
% 0.86/1.00      ( v1_relat_1(sK5) != iProver_top
% 0.86/1.00      | v2_funct_1(sK5) != iProver_top
% 0.86/1.00      | sP0_iProver_split = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_832,plain,
% 0.86/1.00      ( v1_relat_1(sK5) != iProver_top
% 0.86/1.00      | v2_funct_1(sK5) != iProver_top
% 0.86/1.00      | sP0_iProver_split = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1238,plain,
% 0.86/1.00      ( v2_funct_1(sK5) != iProver_top | sP0_iProver_split = iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1087,c_832,c_1204,c_1206]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_258,plain,
% 0.86/1.00      ( ~ v1_relat_1(X0)
% 0.86/1.00      | ~ v2_funct_1(X0)
% 0.86/1.00      | k2_funct_1(k2_funct_1(X0)) = X0
% 0.86/1.00      | sK4 != X0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_259,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | ~ v2_funct_1(sK4)
% 0.86/1.00      | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_258]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_780,plain,
% 0.86/1.00      ( ~ v1_relat_1(sK4)
% 0.86/1.00      | ~ v2_funct_1(sK4)
% 0.86/1.00      | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_259]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1091,plain,
% 0.86/1.00      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 0.86/1.00      | v1_relat_1(sK4) != iProver_top
% 0.86/1.00      | v2_funct_1(sK4) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_6,negated_conjecture,
% 0.86/1.00      ( k2_funct_1(sK4) = sK5 ),
% 0.86/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_788,negated_conjecture,
% 0.86/1.00      ( k2_funct_1(sK4) = sK5 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1137,plain,
% 0.86/1.00      ( k2_funct_1(sK5) = sK4
% 0.86/1.00      | v1_relat_1(sK4) != iProver_top
% 0.86/1.00      | v2_funct_1(sK4) != iProver_top ),
% 0.86/1.00      inference(light_normalisation,[status(thm)],[c_1091,c_788]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1221,plain,
% 0.86/1.00      ( k2_funct_1(sK5) = sK4 | v2_funct_1(sK4) != iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_1137,c_1200,c_1202]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_792,plain,
% 0.86/1.00      ( k9_relat_1(k2_funct_1(sK4),X0_47) = k10_relat_1(sK4,X0_47)
% 0.86/1.00      | ~ sP1_iProver_split ),
% 0.86/1.00      inference(splitting,
% 0.86/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.86/1.00                [c_779]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1093,plain,
% 0.86/1.00      ( k9_relat_1(k2_funct_1(sK4),X0_47) = k10_relat_1(sK4,X0_47)
% 0.86/1.00      | sP1_iProver_split != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1106,plain,
% 0.86/1.00      ( k10_relat_1(sK4,X0_47) = k9_relat_1(sK5,X0_47)
% 0.86/1.00      | sP1_iProver_split != iProver_top ),
% 0.86/1.00      inference(light_normalisation,[status(thm)],[c_1093,c_788]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_790,plain,
% 0.86/1.00      ( k9_relat_1(k2_funct_1(sK5),X0_47) = k10_relat_1(sK5,X0_47)
% 0.86/1.00      | ~ sP0_iProver_split ),
% 0.86/1.00      inference(splitting,
% 0.86/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.86/1.00                [c_783]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1088,plain,
% 0.86/1.00      ( k9_relat_1(k2_funct_1(sK5),X0_47) = k10_relat_1(sK5,X0_47)
% 0.86/1.00      | sP0_iProver_split != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_5,negated_conjecture,
% 0.86/1.00      ( ~ v23_waybel_0(sK5,sK3,sK2) ),
% 0.86/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_789,negated_conjecture,
% 0.86/1.00      ( ~ v23_waybel_0(sK5,sK3,sK2) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1082,plain,
% 0.86/1.00      ( v23_waybel_0(sK5,sK3,sK2) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_9,negated_conjecture,
% 0.86/1.00      ( v23_waybel_0(sK4,sK2,sK3) ),
% 0.86/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_787,negated_conjecture,
% 0.86/1.00      ( v23_waybel_0(sK4,sK2,sK3) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1083,plain,
% 0.86/1.00      ( v23_waybel_0(sK4,sK2,sK3) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  % SZS output end Saturation for theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  ------                               Statistics
% 0.86/1.00  
% 0.86/1.00  ------ General
% 0.86/1.00  
% 0.86/1.00  abstr_ref_over_cycles:                  0
% 0.86/1.00  abstr_ref_under_cycles:                 0
% 0.86/1.00  gc_basic_clause_elim:                   0
% 0.86/1.00  forced_gc_time:                         0
% 0.86/1.00  parsing_time:                           0.011
% 0.86/1.00  unif_index_cands_time:                  0.
% 0.86/1.00  unif_index_add_time:                    0.
% 0.86/1.00  orderings_time:                         0.
% 0.86/1.00  out_proof_time:                         0.
% 0.86/1.00  total_time:                             0.075
% 0.86/1.00  num_of_symbols:                         57
% 0.86/1.00  num_of_terms:                           852
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing
% 0.86/1.00  
% 0.86/1.00  num_of_splits:                          2
% 0.86/1.00  num_of_split_atoms:                     2
% 0.86/1.00  num_of_reused_defs:                     0
% 0.86/1.00  num_eq_ax_congr_red:                    11
% 0.86/1.00  num_of_sem_filtered_clauses:            1
% 0.86/1.00  num_of_subtypes:                        6
% 0.86/1.00  monotx_restored_types:                  0
% 0.86/1.00  sat_num_of_epr_types:                   0
% 0.86/1.00  sat_num_of_non_cyclic_types:            0
% 0.86/1.00  sat_guarded_non_collapsed_types:        0
% 0.86/1.00  num_pure_diseq_elim:                    0
% 0.86/1.00  simp_replaced_by:                       0
% 0.86/1.00  res_preprocessed:                       73
% 0.86/1.00  prep_upred:                             0
% 0.86/1.00  prep_unflattend:                        10
% 0.86/1.00  smt_new_axioms:                         0
% 0.86/1.00  pred_elim_cands:                        5
% 0.86/1.00  pred_elim:                              2
% 0.86/1.00  pred_elim_cl:                           -1
% 0.86/1.00  pred_elim_cycles:                       6
% 0.86/1.00  merged_defs:                            0
% 0.86/1.00  merged_defs_ncl:                        0
% 0.86/1.00  bin_hyper_res:                          0
% 0.86/1.00  prep_cycles:                            3
% 0.86/1.00  pred_elim_time:                         0.012
% 0.86/1.00  splitting_time:                         0.
% 0.86/1.00  sem_filter_time:                        0.
% 0.86/1.00  monotx_time:                            0.
% 0.86/1.00  subtype_inf_time:                       0.
% 0.86/1.00  
% 0.86/1.00  ------ Problem properties
% 0.86/1.00  
% 0.86/1.00  clauses:                                15
% 0.86/1.00  conjectures:                            3
% 0.86/1.00  epr:                                    4
% 0.86/1.00  horn:                                   15
% 0.86/1.00  ground:                                 9
% 0.86/1.00  unary:                                  3
% 0.86/1.00  binary:                                 6
% 0.86/1.00  lits:                                   33
% 0.86/1.00  lits_eq:                                11
% 0.86/1.00  fd_pure:                                0
% 0.86/1.00  fd_pseudo:                              0
% 0.86/1.00  fd_cond:                                0
% 0.86/1.00  fd_pseudo_cond:                         0
% 0.86/1.00  ac_symbols:                             0
% 0.86/1.00  
% 0.86/1.00  ------ Propositional Solver
% 0.86/1.00  
% 0.86/1.00  prop_solver_calls:                      23
% 0.86/1.00  prop_fast_solver_calls:                 495
% 0.86/1.00  smt_solver_calls:                       0
% 0.86/1.00  smt_fast_solver_calls:                  0
% 0.86/1.00  prop_num_of_clauses:                    336
% 0.86/1.00  prop_preprocess_simplified:             1785
% 0.86/1.00  prop_fo_subsumed:                       10
% 0.86/1.00  prop_solver_time:                       0.
% 0.86/1.00  smt_solver_time:                        0.
% 0.86/1.00  smt_fast_solver_time:                   0.
% 0.86/1.00  prop_fast_solver_time:                  0.
% 0.86/1.00  prop_unsat_core_time:                   0.
% 0.86/1.00  
% 0.86/1.00  ------ QBF
% 0.86/1.00  
% 0.86/1.00  qbf_q_res:                              0
% 0.86/1.00  qbf_num_tautologies:                    0
% 0.86/1.00  qbf_prep_cycles:                        0
% 0.86/1.00  
% 0.86/1.00  ------ BMC1
% 0.86/1.00  
% 0.86/1.00  bmc1_current_bound:                     -1
% 0.86/1.00  bmc1_last_solved_bound:                 -1
% 0.86/1.00  bmc1_unsat_core_size:                   -1
% 0.86/1.00  bmc1_unsat_core_parents_size:           -1
% 0.86/1.00  bmc1_merge_next_fun:                    0
% 0.86/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.86/1.00  
% 0.86/1.00  ------ Instantiation
% 0.86/1.00  
% 0.86/1.00  inst_num_of_clauses:                    85
% 0.86/1.00  inst_num_in_passive:                    12
% 0.86/1.00  inst_num_in_active:                     67
% 0.86/1.00  inst_num_in_unprocessed:                6
% 0.86/1.00  inst_num_of_loops:                      80
% 0.86/1.00  inst_num_of_learning_restarts:          0
% 0.86/1.00  inst_num_moves_active_passive:          9
% 0.86/1.00  inst_lit_activity:                      0
% 0.86/1.00  inst_lit_activity_moves:                0
% 0.86/1.00  inst_num_tautologies:                   0
% 0.86/1.00  inst_num_prop_implied:                  0
% 0.86/1.00  inst_num_existing_simplified:           0
% 0.86/1.00  inst_num_eq_res_simplified:             0
% 0.86/1.00  inst_num_child_elim:                    0
% 0.86/1.00  inst_num_of_dismatching_blockings:      4
% 0.86/1.00  inst_num_of_non_proper_insts:           54
% 0.86/1.00  inst_num_of_duplicates:                 0
% 0.86/1.00  inst_inst_num_from_inst_to_res:         0
% 0.86/1.00  inst_dismatching_checking_time:         0.
% 0.86/1.00  
% 0.86/1.00  ------ Resolution
% 0.86/1.00  
% 0.86/1.00  res_num_of_clauses:                     0
% 0.86/1.00  res_num_in_passive:                     0
% 0.86/1.00  res_num_in_active:                      0
% 0.86/1.00  res_num_of_loops:                       76
% 0.86/1.00  res_forward_subset_subsumed:            14
% 0.86/1.00  res_backward_subset_subsumed:           0
% 0.86/1.00  res_forward_subsumed:                   0
% 0.86/1.00  res_backward_subsumed:                  0
% 0.86/1.00  res_forward_subsumption_resolution:     0
% 0.86/1.00  res_backward_subsumption_resolution:    0
% 0.86/1.00  res_clause_to_clause_subsumption:       32
% 0.86/1.00  res_orphan_elimination:                 0
% 0.86/1.00  res_tautology_del:                      16
% 0.86/1.00  res_num_eq_res_simplified:              0
% 0.86/1.00  res_num_sel_changes:                    0
% 0.86/1.00  res_moves_from_active_to_pass:          0
% 0.86/1.00  
% 0.86/1.00  ------ Superposition
% 0.86/1.00  
% 0.86/1.00  sup_time_total:                         0.
% 0.86/1.00  sup_time_generating:                    0.
% 0.86/1.00  sup_time_sim_full:                      0.
% 0.86/1.00  sup_time_sim_immed:                     0.
% 0.86/1.00  
% 0.86/1.00  sup_num_of_clauses:                     15
% 0.86/1.00  sup_num_in_active:                      15
% 0.86/1.00  sup_num_in_passive:                     0
% 0.86/1.00  sup_num_of_loops:                       15
% 0.86/1.00  sup_fw_superposition:                   0
% 0.86/1.00  sup_bw_superposition:                   0
% 0.86/1.00  sup_immediate_simplified:               0
% 0.86/1.00  sup_given_eliminated:                   0
% 0.86/1.00  comparisons_done:                       0
% 0.86/1.00  comparisons_avoided:                    0
% 0.86/1.00  
% 0.86/1.00  ------ Simplifications
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  sim_fw_subset_subsumed:                 0
% 0.86/1.00  sim_bw_subset_subsumed:                 0
% 0.86/1.00  sim_fw_subsumed:                        0
% 0.86/1.00  sim_bw_subsumed:                        0
% 0.86/1.00  sim_fw_subsumption_res:                 0
% 0.86/1.00  sim_bw_subsumption_res:                 0
% 0.86/1.00  sim_tautology_del:                      0
% 0.86/1.00  sim_eq_tautology_del:                   0
% 0.86/1.00  sim_eq_res_simp:                        0
% 0.86/1.00  sim_fw_demodulated:                     0
% 0.86/1.00  sim_bw_demodulated:                     0
% 0.86/1.00  sim_light_normalised:                   2
% 0.86/1.00  sim_joinable_taut:                      0
% 0.86/1.00  sim_joinable_simp:                      0
% 0.86/1.00  sim_ac_normalised:                      0
% 0.86/1.00  sim_smt_subsumption:                    0
% 0.86/1.00  
%------------------------------------------------------------------------------
