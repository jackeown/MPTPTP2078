%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:12 EST 2020

% Result     : CounterSatisfiable 2.73s
% Output     : Saturation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  310 (4655 expanded)
%              Number of clauses        :  230 (1167 expanded)
%              Number of leaves         :   28 (1206 expanded)
%              Depth                    :   22
%              Number of atoms          : 1402 (34140 expanded)
%              Number of equality atoms :  326 (1772 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),sK2,k8_tmap_1(X0,sK2))
          | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2)))
          | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2)) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X1,k8_tmap_1(sK1,X1))
            | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1)))
            | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1)) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) )
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f45,f44])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X2,X0] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X0] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X2,X0] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f78,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
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

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4029,plain,
    ( k5_tmap_1(X0_56,X0_55) = k5_tmap_1(X1_56,X0_55)
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_4028,plain,
    ( u1_pre_topc(X0_56) = u1_pre_topc(X1_56)
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_4015,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_4012,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2243,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_2244,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_2243])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2244,c_31,c_29])).

cnf(c_3993,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0_55)) = k5_tmap_1(sK1,X0_55) ),
    inference(subtyping,[status(esa)],[c_2248])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1441,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_1442,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1441])).

cnf(c_1444,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1442,c_31,c_30,c_29])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1444])).

cnf(c_2337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
    inference(unflattening,[status(thm)],[c_2336])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1452,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_1453,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1452])).

cnf(c_2341,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2337,c_31,c_30,c_29,c_1453])).

cnf(c_2342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
    inference(renaming,[status(thm)],[c_2341])).

cnf(c_3988,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_55) ),
    inference(subtyping,[status(esa)],[c_2342])).

cnf(c_350,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_346,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_345,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_342,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_334,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_332,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_330,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4008,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1444])).

cnf(c_2379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_2378])).

cnf(c_2383,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_31,c_30,c_29,c_1453])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_2383])).

cnf(c_3986,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_2384])).

cnf(c_4480,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3986])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1395,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_1396,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1395])).

cnf(c_1398,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1396,c_29])).

cnf(c_4001,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_1398])).

cnf(c_4465,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4001])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_2226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_2225])).

cnf(c_2230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2226,c_31,c_29])).

cnf(c_3994,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_2230])).

cnf(c_4472,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3994])).

cnf(c_4822,plain,
    ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_4465,c_4472])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_216,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_25,c_14,c_13,c_12])).

cnf(c_217,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_1365,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_27])).

cnf(c_1366,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1365])).

cnf(c_1368,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1366,c_31,c_30,c_29])).

cnf(c_4004,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_1368])).

cnf(c_4823,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_4822,c_4004])).

cnf(c_5799,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4480,c_4823])).

cnf(c_4478,plain,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3988])).

cnf(c_5722,plain,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4478,c_4823])).

cnf(c_5729,plain,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = k5_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_5722])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1444])).

cnf(c_2400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(unflattening,[status(thm)],[c_2399])).

cnf(c_2404,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2400,c_31,c_30,c_29,c_1453])).

cnf(c_2405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_2404])).

cnf(c_3985,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_2405])).

cnf(c_4481,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3985])).

cnf(c_5645,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4481,c_4823])).

cnf(c_5652,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_5645])).

cnf(c_2315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1444])).

cnf(c_2316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_2315])).

cnf(c_2320,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2316,c_31,c_30,c_29,c_1453])).

cnf(c_2321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_2320])).

cnf(c_3989,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_2321])).

cnf(c_4477,plain,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = u1_struct_0(k8_tmap_1(sK1,sK2))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3989])).

cnf(c_5533,plain,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = u1_struct_0(sK1)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4477,c_4823])).

cnf(c_5540,plain,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = u1_struct_0(sK1)
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_5533])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_1444])).

cnf(c_2358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_2357])).

cnf(c_2362,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_31,c_30,c_29,c_1453])).

cnf(c_2363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_2362])).

cnf(c_3987,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_2363])).

cnf(c_4479,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3987])).

cnf(c_5525,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4479,c_4823])).

cnf(c_2297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_30])).

cnf(c_2298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_2297])).

cnf(c_2302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_31,c_29])).

cnf(c_3990,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_2302])).

cnf(c_4476,plain,
    ( k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3990])).

cnf(c_4892,plain,
    ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_4465,c_4476])).

cnf(c_2279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_2280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_2279])).

cnf(c_2284,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2280,c_31,c_29])).

cnf(c_3991,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) ),
    inference(subtyping,[status(esa)],[c_2284])).

cnf(c_4475,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3991])).

cnf(c_5284,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4892,c_4475])).

cnf(c_5291,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5284,c_4004,c_4823])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1397,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_5373,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5291,c_34,c_1397])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_189,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_25])).

cnf(c_190,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_1384,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_27])).

cnf(c_1385,plain,
    ( ~ v2_pre_topc(sK1)
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1384])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1387,plain,
    ( v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1385,c_31,c_30,c_29,c_28])).

cnf(c_4002,plain,
    ( v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) ),
    inference(subtyping,[status(esa)],[c_1387])).

cnf(c_4464,plain,
    ( v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4002])).

cnf(c_4496,plain,
    ( v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4464,c_4004])).

cnf(c_5261,plain,
    ( v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_4496])).

cnf(c_22,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1340,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_1341,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1340])).

cnf(c_1343,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_31,c_30,c_29,c_28])).

cnf(c_1405,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_1343])).

cnf(c_4000,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_1405])).

cnf(c_4466,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4000])).

cnf(c_4517,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4466,c_4004])).

cnf(c_4957,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4517,c_4823])).

cnf(c_5260,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_4957])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_198,plain,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_25])).

cnf(c_199,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_1373,plain,
    ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_27])).

cnf(c_1374,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1373])).

cnf(c_1376,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1374,c_31,c_30,c_29,c_28])).

cnf(c_4003,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) ),
    inference(subtyping,[status(esa)],[c_1376])).

cnf(c_4463,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4003])).

cnf(c_4524,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4463,c_4004])).

cnf(c_5042,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4524,c_4823])).

cnf(c_5259,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_5042])).

cnf(c_10,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2186,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_2187,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_2186])).

cnf(c_2191,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2187,c_31,c_29])).

cnf(c_3996,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_2191])).

cnf(c_4470,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3996])).

cnf(c_4747,plain,
    ( v1_funct_2(k7_tmap_1(sK1,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_4470])).

cnf(c_5094,plain,
    ( v1_funct_2(k7_tmap_1(sK1,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4747,c_34,c_1397])).

cnf(c_5098,plain,
    ( v1_funct_2(k7_tmap_1(sK1,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5094,c_4823])).

cnf(c_5258,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_5098])).

cnf(c_21,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),X1,k6_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_26,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_401,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK1,sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_402,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_406,plain,
    ( v2_struct_0(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_pre_topc(sK2,X0)
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_28])).

cnf(c_407,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_430,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_407,c_25])).

cnf(c_1544,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
    | sK2 != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_430])).

cnf(c_1545,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1544])).

cnf(c_1547,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_31,c_30,c_29,c_1366])).

cnf(c_1548,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(renaming,[status(thm)],[c_1547])).

cnf(c_1902,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(resolution_lifted,[status(thm)],[c_1548,c_1387])).

cnf(c_3997,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_1902])).

cnf(c_4469,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3997])).

cnf(c_4587,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4469,c_4004])).

cnf(c_5156,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4587,c_4823])).

cnf(c_5257,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_5156])).

cnf(c_2261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_2262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_2261])).

cnf(c_2266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_31,c_29])).

cnf(c_3992,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) ),
    inference(subtyping,[status(esa)],[c_2266])).

cnf(c_4474,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3992])).

cnf(c_4752,plain,
    ( v1_funct_1(k7_tmap_1(sK1,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_4474])).

cnf(c_5256,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_4752])).

cnf(c_2204,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_1444])).

cnf(c_2205,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_2204])).

cnf(c_2209,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2205,c_31,c_30,c_29,c_1453])).

cnf(c_2210,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_2209])).

cnf(c_3995,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_2210])).

cnf(c_4471,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3995])).

cnf(c_5162,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4471,c_4823])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_383,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

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
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_pre_topc(X6,X7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v2_pre_topc(X7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(X7)
    | X3 = X0
    | k9_tmap_1(X7,X6) != X0
    | k3_struct_0(X7) != X3
    | u1_struct_0(X7) != X5
    | u1_struct_0(X7) != X4
    | u1_struct_0(X7) != X1
    | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_456,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_16,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_460,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k3_struct_0(X0))
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_16,c_383])).

cnf(c_461,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_490,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_461,c_17,c_15])).

cnf(c_1317,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_490,c_27])).

cnf(c_1318,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1317])).

cnf(c_1320,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1318,c_31,c_30,c_29,c_28])).

cnf(c_1321,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1320])).

cnf(c_1614,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_383,c_1321])).

cnf(c_2462,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1614,c_29])).

cnf(c_2463,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_2462])).

cnf(c_2465,plain,
    ( ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2463,c_31])).

cnf(c_2466,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_2465])).

cnf(c_3984,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_2466])).

cnf(c_4482,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3984])).

cnf(c_4099,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3984])).

cnf(c_5102,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4482,c_4099,c_4823])).

cnf(c_4473,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0_55)) = k5_tmap_1(sK1,X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3993])).

cnf(c_4896,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_4465,c_4473])).

cnf(c_4897,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4896,c_4004])).

cnf(c_1354,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_1355,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1354])).

cnf(c_1357,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_31,c_30,c_29])).

cnf(c_4005,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_1357])).

cnf(c_4462,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_4826,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4823,c_4462])).

cnf(c_1419,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_1420,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1419])).

cnf(c_1422,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1420,c_31,c_30,c_29])).

cnf(c_3998,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(subtyping,[status(esa)],[c_1422])).

cnf(c_4468,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3998])).

cnf(c_4825,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4823,c_4468])).

cnf(c_1408,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_1409,plain,
    ( ~ v2_pre_topc(sK1)
    | v1_funct_1(k9_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1408])).

cnf(c_1411,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1409,c_31,c_30,c_29])).

cnf(c_3999,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1411])).

cnf(c_4467,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3999])).

cnf(c_4007,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_4460,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4007])).

cnf(c_4006,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_4461,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4006])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:14 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 2.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.99  
% 2.73/0.99  ------  iProver source info
% 2.73/0.99  
% 2.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.99  git: non_committed_changes: false
% 2.73/0.99  git: last_make_outside_of_git: false
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     num_symb
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       true
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  ------ Parsing...
% 2.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.99  ------ Proving...
% 2.73/0.99  ------ Problem Properties 
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  clauses                                 25
% 2.73/0.99  conjectures                             2
% 2.73/0.99  EPR                                     2
% 2.73/0.99  Horn                                    18
% 2.73/0.99  unary                                   10
% 2.73/0.99  binary                                  6
% 2.73/0.99  lits                                    53
% 2.73/0.99  lits eq                                 11
% 2.73/0.99  fd_pure                                 0
% 2.73/0.99  fd_pseudo                               0
% 2.73/0.99  fd_cond                                 0
% 2.73/0.99  fd_pseudo_cond                          0
% 2.73/0.99  AC symbols                              0
% 2.73/0.99  
% 2.73/0.99  ------ Schedule dynamic 5 is on 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  Current options:
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     none
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       false
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ Proving...
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  % SZS output start Saturation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  fof(f9,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f30,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f9])).
% 2.73/0.99  
% 2.73/0.99  fof(f31,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f66,plain,(
% 2.73/0.99    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  fof(f13,conjecture,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f14,negated_conjecture,(
% 2.73/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 2.73/0.99    inference(negated_conjecture,[],[f13])).
% 2.73/0.99  
% 2.73/0.99  fof(f37,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f14])).
% 2.73/0.99  
% 2.73/0.99  fof(f38,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f37])).
% 2.73/0.99  
% 2.73/0.99  fof(f45,plain,(
% 2.73/0.99    ( ! [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),sK2,k8_tmap_1(X0,sK2)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f44,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1))))) | ~v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X1,k8_tmap_1(sK1,X1)) | ~v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1))) | ~v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f46,plain,(
% 2.73/0.99    ((~m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2)) | ~v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) | ~v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f45,f44])).
% 2.73/0.99  
% 2.73/0.99  fof(f74,plain,(
% 2.73/0.99    v2_pre_topc(sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f73,plain,(
% 2.73/0.99    ~v2_struct_0(sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f75,plain,(
% 2.73/0.99    l1_pre_topc(sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f7,axiom,(
% 2.73/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f26,plain,(
% 2.73/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f7])).
% 2.73/0.99  
% 2.73/0.99  fof(f27,plain,(
% 2.73/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f26])).
% 2.73/0.99  
% 2.73/0.99  fof(f60,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f77,plain,(
% 2.73/0.99    m1_pre_topc(sK2,sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f61,plain,(
% 2.73/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f6,axiom,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f24,plain,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f6])).
% 2.73/0.99  
% 2.73/0.99  fof(f25,plain,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f24])).
% 2.73/0.99  
% 2.73/0.99  fof(f58,plain,(
% 2.73/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f12,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f36,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f12])).
% 2.73/0.99  
% 2.73/0.99  fof(f72,plain,(
% 2.73/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f65,plain,(
% 2.73/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  fof(f5,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f22,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f5])).
% 2.73/0.99  
% 2.73/0.99  fof(f23,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f22])).
% 2.73/0.99  
% 2.73/0.99  fof(f40,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(nnf_transformation,[],[f23])).
% 2.73/0.99  
% 2.73/0.99  fof(f41,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(rectify,[],[f40])).
% 2.73/0.99  
% 2.73/0.99  fof(f42,plain,(
% 2.73/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f43,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 2.73/0.99  
% 2.73/0.99  fof(f52,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f80,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f52])).
% 2.73/0.99  
% 2.73/0.99  fof(f81,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f80])).
% 2.73/0.99  
% 2.73/0.99  fof(f59,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f4,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f20,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f4])).
% 2.73/0.99  
% 2.73/0.99  fof(f21,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f20])).
% 2.73/0.99  
% 2.73/0.99  fof(f51,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f21])).
% 2.73/0.99  
% 2.73/0.99  fof(f56,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f10,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f32,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f10])).
% 2.73/0.99  
% 2.73/0.99  fof(f33,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f32])).
% 2.73/0.99  
% 2.73/0.99  fof(f67,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f85,plain,(
% 2.73/0.99    ( ! [X2,X0] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f67])).
% 2.73/0.99  
% 2.73/0.99  fof(f76,plain,(
% 2.73/0.99    ~v2_struct_0(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f68,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f84,plain,(
% 2.73/0.99    ( ! [X2,X0] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f68])).
% 2.73/0.99  
% 2.73/0.99  fof(f70,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f82,plain,(
% 2.73/0.99    ( ! [X2,X0] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f70])).
% 2.73/0.99  
% 2.73/0.99  fof(f57,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f69,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f83,plain,(
% 2.73/0.99    ( ! [X2,X0] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f69])).
% 2.73/0.99  
% 2.73/0.99  fof(f78,plain,(
% 2.73/0.99    ~m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2)) | ~v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) | ~v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f1,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f15,plain,(
% 2.73/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f1])).
% 2.73/0.99  
% 2.73/0.99  fof(f47,plain,(
% 2.73/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f15])).
% 2.73/0.99  
% 2.73/0.99  fof(f2,axiom,(
% 2.73/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f16,plain,(
% 2.73/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f2])).
% 2.73/0.99  
% 2.73/0.99  fof(f17,plain,(
% 2.73/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f16])).
% 2.73/0.99  
% 2.73/0.99  fof(f48,plain,(
% 2.73/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f17])).
% 2.73/0.99  
% 2.73/0.99  fof(f3,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f18,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.73/0.99    inference(ennf_transformation,[],[f3])).
% 2.73/0.99  
% 2.73/0.99  fof(f19,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.73/0.99    inference(flattening,[],[f18])).
% 2.73/0.99  
% 2.73/0.99  fof(f39,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.73/0.99    inference(nnf_transformation,[],[f19])).
% 2.73/0.99  
% 2.73/0.99  fof(f49,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f39])).
% 2.73/0.99  
% 2.73/0.99  fof(f11,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f34,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f11])).
% 2.73/0.99  
% 2.73/0.99  fof(f35,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f34])).
% 2.73/0.99  
% 2.73/0.99  fof(f71,plain,(
% 2.73/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f35])).
% 2.73/0.99  
% 2.73/0.99  fof(f8,axiom,(
% 2.73/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f28,plain,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f8])).
% 2.73/0.99  
% 2.73/0.99  fof(f29,plain,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f28])).
% 2.73/0.99  
% 2.73/0.99  fof(f63,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f29])).
% 2.73/0.99  
% 2.73/0.99  fof(f62,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f29])).
% 2.73/0.99  
% 2.73/0.99  fof(f64,plain,(
% 2.73/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f29])).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4029,plain,
% 2.73/0.99      ( k5_tmap_1(X0_56,X0_55) = k5_tmap_1(X1_56,X0_55) | X0_56 != X1_56 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4028,plain,
% 2.73/0.99      ( u1_pre_topc(X0_56) = u1_pre_topc(X1_56) | X0_56 != X1_56 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4015,plain,
% 2.73/0.99      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4012,plain,( X0_58 = X0_58 ),theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_18,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_30,negated_conjecture,
% 2.73/0.99      ( v2_pre_topc(sK1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2243,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.73/0.99      | sK1 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2244,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/0.99      | v2_struct_0(sK1)
% 2.73/0.99      | ~ l1_pre_topc(sK1)
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_2243]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_31,negated_conjecture,
% 2.73/0.99      ( ~ v2_struct_0(sK1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_29,negated_conjecture,
% 2.73/0.99      ( l1_pre_topc(sK1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2248,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_2244,c_31,c_29]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3993,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(sK1,X0_55)) = k5_tmap_1(sK1,X0_55) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_2248]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_13,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_27,negated_conjecture,
% 2.73/0.99      ( m1_pre_topc(sK2,sK1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1441,plain,
% 2.73/0.99      ( ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_pre_topc(k8_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK2 != X1
% 2.73/0.99      | sK1 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1442,plain,
% 2.73/0.99      ( v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | ~ v2_pre_topc(sK1)
% 2.73/0.99      | v2_struct_0(sK1)
% 2.73/0.99      | ~ l1_pre_topc(sK1) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1441]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1444,plain,
% 2.73/0.99      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1442,c_31,c_30,c_29]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2336,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | k8_tmap_1(sK1,sK2) != X1
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1444]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2337,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_2336]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_12,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1452,plain,
% 2.73/0.99      ( ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.73/0.99      | sK2 != X1
% 2.73/0.99      | sK1 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1453,plain,
% 2.73/0.99      ( ~ v2_pre_topc(sK1)
% 2.73/0.99      | v2_struct_0(sK1)
% 2.73/0.99      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | ~ l1_pre_topc(sK1) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1452]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2341,plain,
% 2.73/0.99      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_2337,c_31,c_30,c_29,c_1453]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2342,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_2341]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3988,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_55) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_2342]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_350,plain,
% 2.73/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 2.73/0.99      | v5_pre_topc(X3,X4,X5)
% 2.73/0.99      | X5 != X2
% 2.73/0.99      | X3 != X0
% 2.73/0.99      | X4 != X1 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_346,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_345,plain,
% 2.73/0.99      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_342,plain,
% 2.73/0.99      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_334,plain,
% 2.73/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.73/0.99      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 2.73/0.99      | X8 != X2
% 2.73/0.99      | X6 != X0
% 2.73/0.99      | X7 != X1
% 2.73/0.99      | X9 != X3
% 2.73/0.99      | X10 != X4
% 2.73/0.99      | X11 != X5 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_332,plain,
% 2.73/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_330,plain,
% 2.73/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4008,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_9,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2378,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | k8_tmap_1(sK1,sK2) != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_1444]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2379,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/0.99      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_2378]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2383,plain,
% 2.73/1.00      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2379,c_31,c_30,c_29,c_1453]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2384,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_2383]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3986,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2384]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4480,plain,
% 2.73/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.73/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))))) = iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3986]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_25,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1395,plain,
% 2.73/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | sK2 != X0
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1396,plain,
% 2.73/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1395]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1398,plain,
% 2.73/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1396,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4001,plain,
% 2.73/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1398]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4465,plain,
% 2.73/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4001]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_19,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2225,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2226,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1)
% 2.73/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2225]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2230,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2226,c_31,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3994,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2230]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4472,plain,
% 2.73/1.00      ( u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1)
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3994]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4822,plain,
% 2.73/1.00      ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_4472]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_8,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.73/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_14,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_216,plain,
% 2.73/1.00      ( ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_8,c_25,c_14,c_13,c_12]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_217,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_216]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1365,plain,
% 2.73/1.00      ( ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_217,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1366,plain,
% 2.73/1.00      ( ~ v2_pre_topc(sK1)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1)
% 2.73/1.00      | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1365]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1368,plain,
% 2.73/1.00      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1366,c_31,c_30,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4004,plain,
% 2.73/1.00      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1368]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4823,plain,
% 2.73/1.00      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4822,c_4004]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5799,plain,
% 2.73/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))))) = iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4480,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4478,plain,
% 2.73/1.00      ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_55)
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3988]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5722,plain,
% 2.73/1.00      ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_55)
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4478,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5729,plain,
% 2.73/1.00      ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = k5_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_5722]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2399,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k8_tmap_1(sK1,sK2) != X1
% 2.73/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_1444]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2400,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2399]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2404,plain,
% 2.73/1.00      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2400,c_31,c_30,c_29,c_1453]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2405,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_2404]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3985,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2405]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4481,plain,
% 2.73/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3985]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5645,plain,
% 2.73/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55) = k6_partfun1(u1_struct_0(sK1))
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4481,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5652,plain,
% 2.73/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_5645]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2315,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k8_tmap_1(sK1,sK2) != X1
% 2.73/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_1444]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2316,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2315]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2320,plain,
% 2.73/1.00      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2316,c_31,c_30,c_29,c_1453]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2321,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_2320]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3989,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2321]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4477,plain,
% 2.73/1.00      ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = u1_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3989]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5533,plain,
% 2.73/1.00      ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = u1_struct_0(sK1)
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4477,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5540,plain,
% 2.73/1.00      ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = u1_struct_0(sK1)
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_5533]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_11,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2357,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k8_tmap_1(sK1,sK2) != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_1444]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2358,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2357]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2362,plain,
% 2.73/1.00      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2358,c_31,c_30,c_29,c_1453]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2363,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_2362]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3987,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2363]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4479,plain,
% 2.73/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.73/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3987]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5525,plain,
% 2.73/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55)) = iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4479,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2297,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_30]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2298,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1)
% 2.73/1.00      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2297]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2302,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2298,c_31,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3990,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2302]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4476,plain,
% 2.73/1.00      ( k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1))
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3990]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4892,plain,
% 2.73/1.00      ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_4476]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2279,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2280,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2279]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2284,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2280,c_31,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3991,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2284]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4475,plain,
% 2.73/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3991]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5284,plain,
% 2.73/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) = iProver_top
% 2.73/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4892,c_4475]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5291,plain,
% 2.73/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
% 2.73/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_5284,c_4004,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_34,plain,
% 2.73/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1397,plain,
% 2.73/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.73/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5373,plain,
% 2.73/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_5291,c_34,c_1397]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_23,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_189,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_23,c_25]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_190,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_189]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1384,plain,
% 2.73/1.00      ( ~ v2_pre_topc(X0)
% 2.73/1.00      | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_190,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1385,plain,
% 2.73/1.00      ( ~ v2_pre_topc(sK1)
% 2.73/1.00      | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2))
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1384]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_28,negated_conjecture,
% 2.73/1.00      ( ~ v2_struct_0(sK2) ),
% 2.73/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1387,plain,
% 2.73/1.00      ( v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1385,c_31,c_30,c_29,c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4002,plain,
% 2.73/1.00      ( v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1387]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4464,plain,
% 2.73/1.00      ( v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4002]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4496,plain,
% 2.73/1.00      ( v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4464,c_4004]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5261,plain,
% 2.73/1.00      ( v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2)) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4892,c_4496]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_22,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1340,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1341,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | ~ v2_pre_topc(sK1)
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1340]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1343,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1341,c_31,c_30,c_29,c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1405,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))) ),
% 2.73/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_1343]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4000,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1405]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4466,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4000]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4517,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4466,c_4004]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4957,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4517,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5260,plain,
% 2.73/1.00      ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4892,c_4957]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_20,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_198,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
% 2.73/1.00      | ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_20,c_25]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_199,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_198]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1373,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_199,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1374,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))))))
% 2.73/1.00      | ~ v2_pre_topc(sK1)
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1373]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1376,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1374,c_31,c_30,c_29,c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4003,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1376]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4463,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4003]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4524,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4463,c_4004]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5042,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4524,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5259,plain,
% 2.73/1.00      ( m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4892,c_5042]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_10,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2186,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2187,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2186]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2191,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2187,c_31,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3996,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55)))
% 2.73/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2191]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4470,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3996]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4747,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top
% 2.73/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4004,c_4470]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5094,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4747,c_34,c_1397]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5098,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(sK1,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_5094,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5258,plain,
% 2.73/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4892,c_5098]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_21,plain,
% 2.73/1.00      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),X1,k6_tmap_1(X0,u1_struct_0(X1)))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_26,negated_conjecture,
% 2.73/1.00      ( ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_401,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK1,sK2)
% 2.73/1.00      | sK2 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_402,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_pre_topc(sK2,X0)
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_401]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_406,plain,
% 2.73/1.00      ( v2_struct_0(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ m1_pre_topc(sK2,X0)
% 2.73/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_402,c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_407,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_pre_topc(sK2,X0)
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_406]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_430,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_pre_topc(sK2,X0)
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_407,c_25]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1544,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
% 2.73/1.00      | sK2 != sK2
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_430]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1545,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ v2_pre_topc(sK1)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1)
% 2.73/1.00      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1544]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1547,plain,
% 2.73/1.00      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1545,c_31,c_30,c_29,c_1366]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1548,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 2.73/1.00      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_1547]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1902,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_1548,c_1387]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3997,plain,
% 2.73/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1902]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4469,plain,
% 2.73/1.00      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3997]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4587,plain,
% 2.73/1.00      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4469,c_4004]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5156,plain,
% 2.73/1.00      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4587,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5257,plain,
% 2.73/1.00      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.73/1.00      | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4892,c_5156]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2261,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2262,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(sK1,X0))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2261]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2266,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(sK1,X0)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2262,c_31,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3992,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.73/1.00      | v1_funct_1(k7_tmap_1(sK1,X0_55)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2266]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4474,plain,
% 2.73/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3992]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4752,plain,
% 2.73/1.00      ( v1_funct_1(k7_tmap_1(sK1,u1_struct_0(sK2))) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_4474]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5256,plain,
% 2.73/1.00      ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4892,c_4752]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2204,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k8_tmap_1(sK1,sK2) != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_1444]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2205,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2204]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2209,plain,
% 2.73/1.00      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2205,c_31,c_30,c_29,c_1453]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2210,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_2209]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3995,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55)))
% 2.73/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2210]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4471,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))) = iProver_top
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3995]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5162,plain,
% 2.73/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_55))) = iProver_top
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.73/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4471,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_0,plain,
% 2.73/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1,plain,
% 2.73/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_383,plain,
% 2.73/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 2.73/1.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3,plain,
% 2.73/1.00      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.73/1.00      | ~ v1_funct_2(X5,X2,X3)
% 2.73/1.00      | ~ v1_funct_2(X4,X0,X1)
% 2.73/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.73/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.00      | ~ v1_funct_1(X5)
% 2.73/1.00      | ~ v1_funct_1(X4)
% 2.73/1.00      | v1_xboole_0(X1)
% 2.73/1.00      | v1_xboole_0(X3)
% 2.73/1.00      | X4 = X5 ),
% 2.73/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_24,plain,
% 2.73/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_455,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ v1_funct_2(X3,X4,X5)
% 2.73/1.00      | ~ m1_pre_topc(X6,X7)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.73/1.00      | ~ v2_pre_topc(X7)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X3)
% 2.73/1.00      | v2_struct_0(X7)
% 2.73/1.00      | v2_struct_0(X6)
% 2.73/1.00      | v1_xboole_0(X2)
% 2.73/1.00      | v1_xboole_0(X5)
% 2.73/1.00      | ~ l1_pre_topc(X7)
% 2.73/1.00      | X3 = X0
% 2.73/1.00      | k9_tmap_1(X7,X6) != X0
% 2.73/1.00      | k3_struct_0(X7) != X3
% 2.73/1.00      | u1_struct_0(X7) != X5
% 2.73/1.00      | u1_struct_0(X7) != X4
% 2.73/1.00      | u1_struct_0(X7) != X1
% 2.73/1.00      | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_456,plain,
% 2.73/1.00      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v1_xboole_0(u1_struct_0(X0))
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_16,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_460,plain,
% 2.73/1.00      ( v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 2.73/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.73/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_456,c_16,c_383]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_461,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_460]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_17,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_15,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 2.73/1.00      | ~ v2_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ l1_pre_topc(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_490,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.73/1.00      | ~ m1_pre_topc(X1,X0)
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_461,c_17,c_15]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1317,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_490,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1318,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v2_pre_topc(sK1)
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ l1_pre_topc(sK1)
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1317]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1320,plain,
% 2.73/1.00      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1318,c_31,c_30,c_29,c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1321,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_1320]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1614,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_383,c_1321]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2462,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0)
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_1614,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2463,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_2462]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2465,plain,
% 2.73/1.00      ( ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2463,c_31]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2466,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_2465]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3984,plain,
% 2.73/1.00      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.73/1.00      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.73/1.00      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.73/1.00      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_2466]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4482,plain,
% 2.73/1.00      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.73/1.00      | v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 2.73/1.00      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.73/1.00      | v1_funct_1(k3_struct_0(sK1)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3984]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4099,plain,
% 2.73/1.00      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.73/1.00      | v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 2.73/1.00      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.73/1.00      | v1_funct_1(k3_struct_0(sK1)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3984]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5102,plain,
% 2.73/1.00      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.73/1.00      | v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 2.73/1.00      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.73/1.00      | v1_funct_1(k3_struct_0(sK1)) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4482,c_4099,c_4823]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4473,plain,
% 2.73/1.00      ( u1_pre_topc(k6_tmap_1(sK1,X0_55)) = k5_tmap_1(sK1,X0_55)
% 2.73/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3993]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4896,plain,
% 2.73/1.00      ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4465,c_4473]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4897,plain,
% 2.73/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4896,c_4004]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1354,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1355,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.73/1.00      | ~ v2_pre_topc(sK1)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1354]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1357,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1355,c_31,c_30,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4005,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1357]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4462,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4005]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4826,plain,
% 2.73/1.00      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4823,c_4462]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1419,plain,
% 2.73/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/1.00      | ~ v2_pre_topc(X0)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1420,plain,
% 2.73/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.73/1.00      | ~ v2_pre_topc(sK1)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1419]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1422,plain,
% 2.73/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1420,c_31,c_30,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3998,plain,
% 2.73/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1422]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4468,plain,
% 2.73/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3998]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4825,plain,
% 2.73/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4823,c_4468]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1408,plain,
% 2.73/1.00      ( ~ v2_pre_topc(X0)
% 2.73/1.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ l1_pre_topc(X0)
% 2.73/1.00      | sK2 != X1
% 2.73/1.00      | sK1 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1409,plain,
% 2.73/1.00      ( ~ v2_pre_topc(sK1)
% 2.73/1.00      | v1_funct_1(k9_tmap_1(sK1,sK2))
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | ~ l1_pre_topc(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1408]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1411,plain,
% 2.73/1.00      ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1409,c_31,c_30,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3999,plain,
% 2.73/1.00      ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1411]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4467,plain,
% 2.73/1.00      ( v1_funct_1(k9_tmap_1(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3999]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4007,negated_conjecture,
% 2.73/1.00      ( ~ v2_struct_0(sK2) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4460,plain,
% 2.73/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4007]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4006,negated_conjecture,
% 2.73/1.00      ( ~ v2_struct_0(sK1) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_31]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4461,plain,
% 2.73/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4006]) ).
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS output end Saturation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  ------                               Statistics
% 2.73/1.00  
% 2.73/1.00  ------ General
% 2.73/1.00  
% 2.73/1.00  abstr_ref_over_cycles:                  0
% 2.73/1.00  abstr_ref_under_cycles:                 0
% 2.73/1.00  gc_basic_clause_elim:                   0
% 2.73/1.00  forced_gc_time:                         0
% 2.73/1.00  parsing_time:                           0.021
% 2.73/1.00  unif_index_cands_time:                  0.
% 2.73/1.00  unif_index_add_time:                    0.
% 2.73/1.00  orderings_time:                         0.
% 2.73/1.00  out_proof_time:                         0.
% 2.73/1.00  total_time:                             0.231
% 2.73/1.00  num_of_symbols:                         65
% 2.73/1.00  num_of_terms:                           3810
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing
% 2.73/1.00  
% 2.73/1.00  num_of_splits:                          0
% 2.73/1.00  num_of_split_atoms:                     0
% 2.73/1.00  num_of_reused_defs:                     0
% 2.73/1.00  num_eq_ax_congr_red:                    11
% 2.73/1.00  num_of_sem_filtered_clauses:            7
% 2.73/1.00  num_of_subtypes:                        4
% 2.73/1.00  monotx_restored_types:                  0
% 2.73/1.00  sat_num_of_epr_types:                   0
% 2.73/1.00  sat_num_of_non_cyclic_types:            0
% 2.73/1.00  sat_guarded_non_collapsed_types:        0
% 2.73/1.00  num_pure_diseq_elim:                    0
% 2.73/1.00  simp_replaced_by:                       0
% 2.73/1.00  res_preprocessed:                       148
% 2.73/1.00  prep_upred:                             0
% 2.73/1.00  prep_unflattend:                        64
% 2.73/1.00  smt_new_axioms:                         0
% 2.73/1.00  pred_elim_cands:                        4
% 2.73/1.00  pred_elim:                              8
% 2.73/1.00  pred_elim_cl:                           7
% 2.73/1.00  pred_elim_cycles:                       22
% 2.73/1.00  merged_defs:                            0
% 2.73/1.00  merged_defs_ncl:                        0
% 2.73/1.00  bin_hyper_res:                          0
% 2.73/1.00  prep_cycles:                            4
% 2.73/1.00  pred_elim_time:                         0.105
% 2.73/1.00  splitting_time:                         0.
% 2.73/1.00  sem_filter_time:                        0.
% 2.73/1.00  monotx_time:                            0.
% 2.73/1.00  subtype_inf_time:                       0.
% 2.73/1.00  
% 2.73/1.00  ------ Problem properties
% 2.73/1.00  
% 2.73/1.00  clauses:                                25
% 2.73/1.00  conjectures:                            2
% 2.73/1.00  epr:                                    2
% 2.73/1.00  horn:                                   18
% 2.73/1.00  ground:                                 13
% 2.73/1.00  unary:                                  10
% 2.73/1.00  binary:                                 6
% 2.73/1.00  lits:                                   53
% 2.73/1.00  lits_eq:                                11
% 2.73/1.00  fd_pure:                                0
% 2.73/1.00  fd_pseudo:                              0
% 2.73/1.00  fd_cond:                                0
% 2.73/1.00  fd_pseudo_cond:                         0
% 2.73/1.00  ac_symbols:                             0
% 2.73/1.00  
% 2.73/1.00  ------ Propositional Solver
% 2.73/1.00  
% 2.73/1.00  prop_solver_calls:                      26
% 2.73/1.00  prop_fast_solver_calls:                 1953
% 2.73/1.00  smt_solver_calls:                       0
% 2.73/1.00  smt_fast_solver_calls:                  0
% 2.73/1.00  prop_num_of_clauses:                    1282
% 2.73/1.00  prop_preprocess_simplified:             4943
% 2.73/1.00  prop_fo_subsumed:                       91
% 2.73/1.00  prop_solver_time:                       0.
% 2.73/1.00  smt_solver_time:                        0.
% 2.73/1.00  smt_fast_solver_time:                   0.
% 2.73/1.00  prop_fast_solver_time:                  0.
% 2.73/1.00  prop_unsat_core_time:                   0.
% 2.73/1.00  
% 2.73/1.00  ------ QBF
% 2.73/1.00  
% 2.73/1.00  qbf_q_res:                              0
% 2.73/1.00  qbf_num_tautologies:                    0
% 2.73/1.00  qbf_prep_cycles:                        0
% 2.73/1.00  
% 2.73/1.00  ------ BMC1
% 2.73/1.00  
% 2.73/1.00  bmc1_current_bound:                     -1
% 2.73/1.00  bmc1_last_solved_bound:                 -1
% 2.73/1.00  bmc1_unsat_core_size:                   -1
% 2.73/1.00  bmc1_unsat_core_parents_size:           -1
% 2.73/1.00  bmc1_merge_next_fun:                    0
% 2.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation
% 2.73/1.00  
% 2.73/1.00  inst_num_of_clauses:                    304
% 2.73/1.00  inst_num_in_passive:                    80
% 2.73/1.00  inst_num_in_active:                     199
% 2.73/1.00  inst_num_in_unprocessed:                26
% 2.73/1.00  inst_num_of_loops:                      210
% 2.73/1.00  inst_num_of_learning_restarts:          0
% 2.73/1.00  inst_num_moves_active_passive:          7
% 2.73/1.00  inst_lit_activity:                      0
% 2.73/1.00  inst_lit_activity_moves:                0
% 2.73/1.00  inst_num_tautologies:                   0
% 2.73/1.00  inst_num_prop_implied:                  0
% 2.73/1.00  inst_num_existing_simplified:           0
% 2.73/1.00  inst_num_eq_res_simplified:             0
% 2.73/1.00  inst_num_child_elim:                    0
% 2.73/1.00  inst_num_of_dismatching_blockings:      65
% 2.73/1.00  inst_num_of_non_proper_insts:           273
% 2.73/1.00  inst_num_of_duplicates:                 0
% 2.73/1.00  inst_inst_num_from_inst_to_res:         0
% 2.73/1.00  inst_dismatching_checking_time:         0.
% 2.73/1.00  
% 2.73/1.00  ------ Resolution
% 2.73/1.00  
% 2.73/1.00  res_num_of_clauses:                     0
% 2.73/1.00  res_num_in_passive:                     0
% 2.73/1.00  res_num_in_active:                      0
% 2.73/1.00  res_num_of_loops:                       152
% 2.73/1.00  res_forward_subset_subsumed:            71
% 2.73/1.00  res_backward_subset_subsumed:           4
% 2.73/1.00  res_forward_subsumed:                   0
% 2.73/1.00  res_backward_subsumed:                  2
% 2.73/1.00  res_forward_subsumption_resolution:     9
% 2.73/1.00  res_backward_subsumption_resolution:    1
% 2.73/1.00  res_clause_to_clause_subsumption:       148
% 2.73/1.00  res_orphan_elimination:                 0
% 2.73/1.00  res_tautology_del:                      70
% 2.73/1.00  res_num_eq_res_simplified:              0
% 2.73/1.00  res_num_sel_changes:                    0
% 2.73/1.00  res_moves_from_active_to_pass:          0
% 2.73/1.00  
% 2.73/1.00  ------ Superposition
% 2.73/1.00  
% 2.73/1.00  sup_time_total:                         0.
% 2.73/1.00  sup_time_generating:                    0.
% 2.73/1.00  sup_time_sim_full:                      0.
% 2.73/1.00  sup_time_sim_immed:                     0.
% 2.73/1.00  
% 2.73/1.00  sup_num_of_clauses:                     33
% 2.73/1.00  sup_num_in_active:                      33
% 2.73/1.00  sup_num_in_passive:                     0
% 2.73/1.00  sup_num_of_loops:                       41
% 2.73/1.00  sup_fw_superposition:                   9
% 2.73/1.00  sup_bw_superposition:                   2
% 2.73/1.00  sup_immediate_simplified:               6
% 2.73/1.00  sup_given_eliminated:                   0
% 2.73/1.00  comparisons_done:                       0
% 2.73/1.00  comparisons_avoided:                    0
% 2.73/1.00  
% 2.73/1.00  ------ Simplifications
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  sim_fw_subset_subsumed:                 1
% 2.73/1.00  sim_bw_subset_subsumed:                 1
% 2.73/1.00  sim_fw_subsumed:                        0
% 2.73/1.00  sim_bw_subsumed:                        0
% 2.73/1.00  sim_fw_subsumption_res:                 0
% 2.73/1.00  sim_bw_subsumption_res:                 0
% 2.73/1.00  sim_tautology_del:                      0
% 2.73/1.00  sim_eq_tautology_del:                   0
% 2.73/1.00  sim_eq_res_simp:                        0
% 2.73/1.00  sim_fw_demodulated:                     0
% 2.73/1.00  sim_bw_demodulated:                     8
% 2.73/1.00  sim_light_normalised:                   20
% 2.73/1.00  sim_joinable_taut:                      0
% 2.73/1.00  sim_joinable_simp:                      0
% 2.73/1.00  sim_ac_normalised:                      0
% 2.73/1.00  sim_smt_subsumption:                    0
% 2.73/1.00  
%------------------------------------------------------------------------------
