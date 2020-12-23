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
% DateTime   : Thu Dec  3 12:17:11 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  183 (5241 expanded)
%              Number of clauses        :  125 (1936 expanded)
%              Number of leaves         :   16 (1384 expanded)
%              Depth                    :   26
%              Number of atoms          :  568 (34133 expanded)
%              Number of equality atoms :  276 (12054 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1) )
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                  | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) )
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).

fof(f55,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1002,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1425,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1010,plain,
    ( ~ l1_struct_0(X0_56)
    | u1_struct_0(X0_56) = k2_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1419,plain,
    ( u1_struct_0(X0_56) = k2_struct_0(X0_56)
    | l1_struct_0(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_1654,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1425,c_1419])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1005,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1422,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_1816,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1654,c_1422])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1001,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1426,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_1655,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1426,c_1419])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1006,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1820,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1654,c_1006])).

cnf(c_1860,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1655,c_1820])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1012,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1417,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_1729,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1422,c_1417])).

cnf(c_2177,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1729,c_1654,c_1655])).

cnf(c_2229,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1860,c_2177])).

cnf(c_2249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1816,c_1655,c_2229])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_struct_0(X2)) = k2_struct_0(X1)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1008,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_52)
    | k8_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_52,k2_struct_0(X1_56)) = k2_struct_0(X0_56)
    | k2_struct_0(X1_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1421,plain,
    ( k8_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_52,k2_struct_0(X1_56)) = k2_struct_0(X0_56)
    | k2_struct_0(X1_56) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | l1_struct_0(X1_56) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_2065,plain,
    ( k8_relset_1(u1_struct_0(X0_56),u1_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X0_56),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_1421])).

cnf(c_2089,plain,
    ( k8_relset_1(u1_struct_0(X0_56),k2_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2065,c_1654])).

cnf(c_27,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_266,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_284,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_23])).

cnf(c_285,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_268,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_287,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_23,c_22,c_268])).

cnf(c_1000,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_1818,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1654,c_1000])).

cnf(c_2909,plain,
    ( l1_struct_0(X0_56) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_struct_0(sK1)) != iProver_top
    | k8_relset_1(u1_struct_0(X0_56),k2_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2089,c_27,c_1818])).

cnf(c_2910,plain,
    ( k8_relset_1(u1_struct_0(X0_56),k2_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
    | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2909])).

cnf(c_2915,plain,
    ( k8_relset_1(u1_struct_0(X0_56),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(X0_56)
    | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2910,c_2229])).

cnf(c_2925,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(X0_52,u1_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_2915])).

cnf(c_2931,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(X0_52,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2925,c_1655])).

cnf(c_25,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2955,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(X0_52,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2931,c_25])).

cnf(c_2956,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(X0_52,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2955])).

cnf(c_2965,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_2956])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1014,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1415,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1014])).

cnf(c_1649,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1415])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1015,plain,
    ( ~ v1_relat_1(X0_52)
    | k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1414,plain,
    ( k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_1732,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1649,c_1414])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1418,plain,
    ( k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_2252,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0_53) = k10_relat_1(sK2,X0_53) ),
    inference(superposition,[status(thm)],[c_2249,c_1418])).

cnf(c_2966,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2965,c_1732,c_2252])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1004,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1423,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1817,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1654,c_1423])).

cnf(c_1920,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1817,c_1655])).

cnf(c_2233,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2229,c_1920])).

cnf(c_3420,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2966,c_28,c_2233])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1007,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1819,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1654,c_1007])).

cnf(c_1859,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1655,c_1819])).

cnf(c_2427,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1859,c_2229])).

cnf(c_3432,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3420,c_2427])).

cnf(c_2231,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2229,c_2177])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_348,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_349,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_353,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_21])).

cnf(c_354,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_999,plain,
    ( ~ v1_funct_2(sK2,X0_53,X1_53)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1427,plain,
    ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_3327,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_1427])).

cnf(c_3890,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3327,c_2233,c_2249])).

cnf(c_3892,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3890,c_3420])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_421,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_425,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_21])).

cnf(c_426,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_425])).

cnf(c_996,plain,
    ( ~ v1_funct_2(sK2,X0_53,X1_53)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53 ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_1430,plain,
    ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_3325,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_1430])).

cnf(c_3895,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3325,c_2233,c_2249])).

cnf(c_3899,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3895,c_3420])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1416,plain,
    ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_3904,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3899,c_1416])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_444,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_445,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_21])).

cnf(c_995,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1431,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_1600,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_2357,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_19,c_995,c_1600])).

cnf(c_3909,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3904,c_2357])).

cnf(c_3903,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3899,c_1417])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_458,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_459,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_461,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_21])).

cnf(c_994,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_1432,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_2361,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1432,c_19,c_994,c_1600])).

cnf(c_3912,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3903,c_2361])).

cnf(c_4006,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3432,c_3892,c_3909,c_3912])).

cnf(c_4007,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4006])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 2.34/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.01  
% 2.34/1.01  ------  iProver source info
% 2.34/1.01  
% 2.34/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.01  git: non_committed_changes: false
% 2.34/1.01  git: last_make_outside_of_git: false
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     num_symb
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       true
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  ------ Parsing...
% 2.34/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.01  ------ Proving...
% 2.34/1.01  ------ Problem Properties 
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  clauses                                 22
% 2.34/1.01  conjectures                             7
% 2.34/1.01  EPR                                     3
% 2.34/1.01  Horn                                    21
% 2.34/1.01  unary                                   7
% 2.34/1.01  binary                                  9
% 2.34/1.01  lits                                    55
% 2.34/1.01  lits eq                                 20
% 2.34/1.01  fd_pure                                 0
% 2.34/1.01  fd_pseudo                               0
% 2.34/1.01  fd_cond                                 0
% 2.34/1.01  fd_pseudo_cond                          0
% 2.34/1.01  AC symbols                              0
% 2.34/1.01  
% 2.34/1.01  ------ Schedule dynamic 5 is on 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  Current options:
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     none
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       false
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ Proving...
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS status Theorem for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01   Resolution empty clause
% 2.34/1.01  
% 2.34/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  fof(f13,conjecture,(
% 2.34/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f14,negated_conjecture,(
% 2.34/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.34/1.01    inference(negated_conjecture,[],[f13])).
% 2.34/1.01  
% 2.34/1.01  fof(f31,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f14])).
% 2.34/1.01  
% 2.34/1.01  fof(f32,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f31])).
% 2.34/1.01  
% 2.34/1.01  fof(f35,plain,(
% 2.34/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f34,plain,(
% 2.34/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f33,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f36,plain,(
% 2.34/1.01    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).
% 2.34/1.01  
% 2.34/1.01  fof(f55,plain,(
% 2.34/1.01    l1_struct_0(sK1)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f9,axiom,(
% 2.34/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f24,plain,(
% 2.34/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f9])).
% 2.34/1.01  
% 2.34/1.01  fof(f48,plain,(
% 2.34/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f24])).
% 2.34/1.01  
% 2.34/1.01  fof(f58,plain,(
% 2.34/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f53,plain,(
% 2.34/1.01    l1_struct_0(sK0)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f59,plain,(
% 2.34/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f6,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f20,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f6])).
% 2.34/1.01  
% 2.34/1.01  fof(f43,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f20])).
% 2.34/1.01  
% 2.34/1.01  fof(f12,axiom,(
% 2.34/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f29,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f12])).
% 2.34/1.01  
% 2.34/1.01  fof(f30,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f29])).
% 2.34/1.01  
% 2.34/1.01  fof(f51,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f30])).
% 2.34/1.01  
% 2.34/1.01  fof(f1,axiom,(
% 2.34/1.01    v1_xboole_0(k1_xboole_0)),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f37,plain,(
% 2.34/1.01    v1_xboole_0(k1_xboole_0)),
% 2.34/1.01    inference(cnf_transformation,[],[f1])).
% 2.34/1.01  
% 2.34/1.01  fof(f10,axiom,(
% 2.34/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f25,plain,(
% 2.34/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f10])).
% 2.34/1.01  
% 2.34/1.01  fof(f26,plain,(
% 2.34/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f25])).
% 2.34/1.01  
% 2.34/1.01  fof(f49,plain,(
% 2.34/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f26])).
% 2.34/1.01  
% 2.34/1.01  fof(f54,plain,(
% 2.34/1.01    ~v2_struct_0(sK1)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f4,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f18,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f4])).
% 2.34/1.01  
% 2.34/1.01  fof(f41,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f18])).
% 2.34/1.01  
% 2.34/1.01  fof(f2,axiom,(
% 2.34/1.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f15,plain,(
% 2.34/1.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f2])).
% 2.34/1.01  
% 2.34/1.01  fof(f38,plain,(
% 2.34/1.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f15])).
% 2.34/1.01  
% 2.34/1.01  fof(f7,axiom,(
% 2.34/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f21,plain,(
% 2.34/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f7])).
% 2.34/1.01  
% 2.34/1.01  fof(f44,plain,(
% 2.34/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f21])).
% 2.34/1.01  
% 2.34/1.01  fof(f56,plain,(
% 2.34/1.01    v1_funct_1(sK2)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f57,plain,(
% 2.34/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f61,plain,(
% 2.34/1.01    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f11,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f27,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.34/1.01    inference(ennf_transformation,[],[f11])).
% 2.34/1.01  
% 2.34/1.01  fof(f28,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/1.01    inference(flattening,[],[f27])).
% 2.34/1.01  
% 2.34/1.01  fof(f50,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f28])).
% 2.34/1.01  
% 2.34/1.01  fof(f60,plain,(
% 2.34/1.01    v2_funct_1(sK2)),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f8,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f22,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.34/1.01    inference(ennf_transformation,[],[f8])).
% 2.34/1.01  
% 2.34/1.01  fof(f23,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/1.01    inference(flattening,[],[f22])).
% 2.34/1.01  
% 2.34/1.01  fof(f47,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f23])).
% 2.34/1.01  
% 2.34/1.01  fof(f5,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f19,plain,(
% 2.34/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.01    inference(ennf_transformation,[],[f5])).
% 2.34/1.01  
% 2.34/1.01  fof(f42,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f19])).
% 2.34/1.01  
% 2.34/1.01  fof(f3,axiom,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f16,plain,(
% 2.34/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f3])).
% 2.34/1.01  
% 2.34/1.01  fof(f17,plain,(
% 2.34/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f16])).
% 2.34/1.01  
% 2.34/1.01  fof(f39,plain,(
% 2.34/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f17])).
% 2.34/1.01  
% 2.34/1.01  fof(f40,plain,(
% 2.34/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f17])).
% 2.34/1.01  
% 2.34/1.01  cnf(c_22,negated_conjecture,
% 2.34/1.01      ( l1_struct_0(sK1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1002,negated_conjecture,
% 2.34/1.01      ( l1_struct_0(sK1) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1425,plain,
% 2.34/1.01      ( l1_struct_0(sK1) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_11,plain,
% 2.34/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1010,plain,
% 2.34/1.01      ( ~ l1_struct_0(X0_56) | u1_struct_0(X0_56) = k2_struct_0(X0_56) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1419,plain,
% 2.34/1.01      ( u1_struct_0(X0_56) = k2_struct_0(X0_56)
% 2.34/1.01      | l1_struct_0(X0_56) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1010]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1654,plain,
% 2.34/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1425,c_1419]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_19,negated_conjecture,
% 2.34/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1005,negated_conjecture,
% 2.34/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1422,plain,
% 2.34/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1816,plain,
% 2.34/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1654,c_1422]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_24,negated_conjecture,
% 2.34/1.01      ( l1_struct_0(sK0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1001,negated_conjecture,
% 2.34/1.01      ( l1_struct_0(sK0) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1426,plain,
% 2.34/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1655,plain,
% 2.34/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1426,c_1419]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_18,negated_conjecture,
% 2.34/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1006,negated_conjecture,
% 2.34/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1820,plain,
% 2.34/1.01      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1654,c_1006]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1860,plain,
% 2.34/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1655,c_1820]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_6,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1012,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.34/1.01      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1417,plain,
% 2.34/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1729,plain,
% 2.34/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1422,c_1417]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2177,plain,
% 2.34/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_1729,c_1654,c_1655]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2229,plain,
% 2.34/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_1860,c_2177]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2249,plain,
% 2.34/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_1816,c_1655,c_2229]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_15,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.34/1.01      | ~ l1_struct_0(X1)
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_struct_0(X2)) = k2_struct_0(X1)
% 2.34/1.01      | k2_struct_0(X2) = k1_xboole_0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1008,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 2.34/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 2.34/1.01      | ~ l1_struct_0(X1_56)
% 2.34/1.01      | ~ l1_struct_0(X0_56)
% 2.34/1.01      | ~ v1_funct_1(X0_52)
% 2.34/1.01      | k8_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_52,k2_struct_0(X1_56)) = k2_struct_0(X0_56)
% 2.34/1.01      | k2_struct_0(X1_56) = k1_xboole_0 ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1421,plain,
% 2.34/1.01      ( k8_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_52,k2_struct_0(X1_56)) = k2_struct_0(X0_56)
% 2.34/1.01      | k2_struct_0(X1_56) = k1_xboole_0
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 2.34/1.01      | l1_struct_0(X0_56) != iProver_top
% 2.34/1.01      | l1_struct_0(X1_56) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2065,plain,
% 2.34/1.01      ( k8_relset_1(u1_struct_0(X0_56),u1_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
% 2.34/1.01      | k2_struct_0(sK1) = k1_xboole_0
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(X0_56),u1_struct_0(sK1)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
% 2.34/1.01      | l1_struct_0(X0_56) != iProver_top
% 2.34/1.01      | l1_struct_0(sK1) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1654,c_1421]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2089,plain,
% 2.34/1.01      ( k8_relset_1(u1_struct_0(X0_56),k2_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
% 2.34/1.01      | k2_struct_0(sK1) = k1_xboole_0
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_struct_0(sK1)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
% 2.34/1.01      | l1_struct_0(X0_56) != iProver_top
% 2.34/1.01      | l1_struct_0(sK1) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_2065,c_1654]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_27,plain,
% 2.34/1.01      ( l1_struct_0(sK1) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_0,plain,
% 2.34/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_12,plain,
% 2.34/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_266,plain,
% 2.34/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_23,negated_conjecture,
% 2.34/1.01      ( ~ v2_struct_0(sK1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_284,plain,
% 2.34/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_266,c_23]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_285,plain,
% 2.34/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_284]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_268,plain,
% 2.34/1.01      ( v2_struct_0(sK1)
% 2.34/1.01      | ~ l1_struct_0(sK1)
% 2.34/1.01      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_266]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_287,plain,
% 2.34/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_285,c_23,c_22,c_268]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1000,plain,
% 2.34/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_287]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1818,plain,
% 2.34/1.01      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1654,c_1000]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2909,plain,
% 2.34/1.01      ( l1_struct_0(X0_56) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_struct_0(sK1)) != iProver_top
% 2.34/1.01      | k8_relset_1(u1_struct_0(X0_56),k2_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_2089,c_27,c_1818]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2910,plain,
% 2.34/1.01      ( k8_relset_1(u1_struct_0(X0_56),k2_struct_0(sK1),X0_52,k2_struct_0(sK1)) = k2_struct_0(X0_56)
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_struct_0(sK1)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_struct_0(sK1)))) != iProver_top
% 2.34/1.01      | l1_struct_0(X0_56) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_2909]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2915,plain,
% 2.34/1.01      ( k8_relset_1(u1_struct_0(X0_56),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(X0_56)
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(X0_56),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),k2_relat_1(sK2)))) != iProver_top
% 2.34/1.01      | l1_struct_0(X0_56) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_2910,c_2229]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2925,plain,
% 2.34/1.01      ( k8_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.34/1.01      | v1_funct_2(X0_52,u1_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.34/1.01      | l1_struct_0(sK0) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1655,c_2915]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2931,plain,
% 2.34/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.34/1.01      | v1_funct_2(X0_52,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.34/1.01      | l1_struct_0(sK0) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_2925,c_1655]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_25,plain,
% 2.34/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2955,plain,
% 2.34/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.34/1.01      | v1_funct_2(X0_52,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2931,c_25]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2956,plain,
% 2.34/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_52,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.34/1.01      | v1_funct_2(X0_52,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.34/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_2955]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2965,plain,
% 2.34/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.34/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_2249,c_2956]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1014,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.34/1.01      | v1_relat_1(X0_52) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1415,plain,
% 2.34/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.34/1.01      | v1_relat_1(X0_52) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1014]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1649,plain,
% 2.34/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1422,c_1415]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1,plain,
% 2.34/1.01      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1015,plain,
% 2.34/1.01      ( ~ v1_relat_1(X0_52)
% 2.34/1.01      | k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1414,plain,
% 2.34/1.01      ( k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52)
% 2.34/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1732,plain,
% 2.34/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_1649,c_1414]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_7,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.34/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1011,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.34/1.01      | k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1418,plain,
% 2.34/1.01      ( k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53)
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2252,plain,
% 2.34/1.01      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0_53) = k10_relat_1(sK2,X0_53) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_2249,c_1418]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2966,plain,
% 2.34/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.34/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_2965,c_1732,c_2252]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_21,negated_conjecture,
% 2.34/1.01      ( v1_funct_1(sK2) ),
% 2.34/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_28,plain,
% 2.34/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_20,negated_conjecture,
% 2.34/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1004,negated_conjecture,
% 2.34/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1423,plain,
% 2.34/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1817,plain,
% 2.34/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1654,c_1423]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1920,plain,
% 2.34/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_1817,c_1655]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2233,plain,
% 2.34/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_2229,c_1920]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3420,plain,
% 2.34/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_2966,c_28,c_2233]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_16,negated_conjecture,
% 2.34/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.34/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1007,negated_conjecture,
% 2.34/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.34/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1819,plain,
% 2.34/1.01      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.34/1.01      | k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1654,c_1007]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1859,plain,
% 2.34/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.34/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_1655,c_1819]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2427,plain,
% 2.34/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
% 2.34/1.01      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_1859,c_2229]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3432,plain,
% 2.34/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k1_relat_1(sK2)
% 2.34/1.01      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_3420,c_2427]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2231,plain,
% 2.34/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(demodulation,[status(thm)],[c_2229,c_2177]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_13,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v2_funct_1(X0)
% 2.34/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.34/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.34/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_17,negated_conjecture,
% 2.34/1.01      ( v2_funct_1(sK2) ),
% 2.34/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_348,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.34/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.34/1.01      | sK2 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_349,plain,
% 2.34/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.34/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.01      | ~ v1_funct_1(sK2)
% 2.34/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.34/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_348]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_353,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 2.34/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.34/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.34/1.01      inference(global_propositional_subsumption,[status(thm)],[c_349,c_21]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_354,plain,
% 2.34/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.34/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.34/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_353]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_999,plain,
% 2.34/1.01      ( ~ v1_funct_2(sK2,X0_53,X1_53)
% 2.34/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.34/1.01      | k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.34/1.01      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_354]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1427,plain,
% 2.34/1.01      ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.34/1.01      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
% 2.34/1.01      | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
% 2.34/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_999]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3327,plain,
% 2.34/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.34/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_2231,c_1427]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3890,plain,
% 2.34/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3327,c_2233,c_2249]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3892,plain,
% 2.34/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_3890,c_3420]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_8,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v2_funct_1(X0)
% 2.34/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.34/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_420,plain,
% 2.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.34/1.01      | sK2 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_421,plain,
% 2.34/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.34/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.34/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.01      | ~ v1_funct_1(sK2)
% 2.34/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_420]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_425,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.34/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 2.34/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.34/1.01      inference(global_propositional_subsumption,[status(thm)],[c_421,c_21]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_426,plain,
% 2.34/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.34/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.34/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_425]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_996,plain,
% 2.34/1.01      ( ~ v1_funct_2(sK2,X0_53,X1_53)
% 2.34/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.34/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.34/1.01      | k2_relset_1(X0_53,X1_53,sK2) != X1_53 ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_426]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1430,plain,
% 2.34/1.01      ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.34/1.01      | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
% 2.34/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.34/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3325,plain,
% 2.34/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.34/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.34/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_2231,c_1430]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3895,plain,
% 2.34/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3325,c_2233,c_2249]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3899,plain,
% 2.34/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_3895,c_3420]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1013,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.34/1.01      | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1416,plain,
% 2.34/1.01      ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
% 2.34/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3904,plain,
% 2.34/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_3899,c_1416]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v2_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_444,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.34/1.01      | sK2 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_445,plain,
% 2.34/1.01      ( ~ v1_funct_1(sK2)
% 2.34/1.01      | ~ v1_relat_1(sK2)
% 2.34/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_444]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_447,plain,
% 2.34/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(global_propositional_subsumption,[status(thm)],[c_445,c_21]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_995,plain,
% 2.34/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_447]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1431,plain,
% 2.34/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.34/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1600,plain,
% 2.34/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.34/1.01      | v1_relat_1(sK2) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_1014]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2357,plain,
% 2.34/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1431,c_19,c_995,c_1600]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3909,plain,
% 2.34/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_3904,c_2357]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3903,plain,
% 2.34/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_3899,c_1417]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v2_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_458,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.34/1.01      | sK2 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_459,plain,
% 2.34/1.01      ( ~ v1_funct_1(sK2)
% 2.34/1.01      | ~ v1_relat_1(sK2)
% 2.34/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_458]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_461,plain,
% 2.34/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(global_propositional_subsumption,[status(thm)],[c_459,c_21]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_994,plain,
% 2.34/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(subtyping,[status(esa)],[c_461]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1432,plain,
% 2.34/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.34/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2361,plain,
% 2.34/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1432,c_19,c_994,c_1600]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3912,plain,
% 2.34/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_3903,c_2361]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4006,plain,
% 2.34/1.01      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.34/1.01      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.34/1.01      inference(light_normalisation,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3432,c_3892,c_3909,c_3912]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4007,plain,
% 2.34/1.01      ( $false ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_4006]) ).
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  ------                               Statistics
% 2.34/1.01  
% 2.34/1.01  ------ General
% 2.34/1.01  
% 2.34/1.01  abstr_ref_over_cycles:                  0
% 2.34/1.01  abstr_ref_under_cycles:                 0
% 2.34/1.01  gc_basic_clause_elim:                   0
% 2.34/1.01  forced_gc_time:                         0
% 2.34/1.01  parsing_time:                           0.011
% 2.34/1.01  unif_index_cands_time:                  0.
% 2.34/1.01  unif_index_add_time:                    0.
% 2.34/1.01  orderings_time:                         0.
% 2.34/1.01  out_proof_time:                         0.011
% 2.34/1.01  total_time:                             0.162
% 2.34/1.01  num_of_symbols:                         57
% 2.34/1.01  num_of_terms:                           3031
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing
% 2.34/1.01  
% 2.34/1.01  num_of_splits:                          0
% 2.34/1.01  num_of_split_atoms:                     0
% 2.34/1.01  num_of_reused_defs:                     0
% 2.34/1.01  num_eq_ax_congr_red:                    11
% 2.34/1.01  num_of_sem_filtered_clauses:            1
% 2.34/1.01  num_of_subtypes:                        5
% 2.34/1.01  monotx_restored_types:                  0
% 2.34/1.01  sat_num_of_epr_types:                   0
% 2.34/1.01  sat_num_of_non_cyclic_types:            0
% 2.34/1.01  sat_guarded_non_collapsed_types:        0
% 2.34/1.01  num_pure_diseq_elim:                    0
% 2.34/1.01  simp_replaced_by:                       0
% 2.34/1.01  res_preprocessed:                       132
% 2.34/1.01  prep_upred:                             0
% 2.34/1.01  prep_unflattend:                        19
% 2.34/1.01  smt_new_axioms:                         0
% 2.34/1.01  pred_elim_cands:                        5
% 2.34/1.01  pred_elim:                              3
% 2.34/1.01  pred_elim_cl:                           3
% 2.34/1.01  pred_elim_cycles:                       8
% 2.34/1.01  merged_defs:                            0
% 2.34/1.01  merged_defs_ncl:                        0
% 2.34/1.01  bin_hyper_res:                          0
% 2.34/1.01  prep_cycles:                            4
% 2.34/1.01  pred_elim_time:                         0.012
% 2.34/1.01  splitting_time:                         0.
% 2.34/1.01  sem_filter_time:                        0.
% 2.34/1.01  monotx_time:                            0.
% 2.34/1.01  subtype_inf_time:                       0.001
% 2.34/1.01  
% 2.34/1.01  ------ Problem properties
% 2.34/1.01  
% 2.34/1.01  clauses:                                22
% 2.34/1.01  conjectures:                            7
% 2.34/1.01  epr:                                    3
% 2.34/1.01  horn:                                   21
% 2.34/1.01  ground:                                 10
% 2.34/1.01  unary:                                  7
% 2.34/1.01  binary:                                 9
% 2.34/1.01  lits:                                   55
% 2.34/1.01  lits_eq:                                20
% 2.34/1.01  fd_pure:                                0
% 2.34/1.01  fd_pseudo:                              0
% 2.34/1.01  fd_cond:                                0
% 2.34/1.01  fd_pseudo_cond:                         0
% 2.34/1.01  ac_symbols:                             0
% 2.34/1.01  
% 2.34/1.01  ------ Propositional Solver
% 2.34/1.01  
% 2.34/1.01  prop_solver_calls:                      29
% 2.34/1.01  prop_fast_solver_calls:                 1044
% 2.34/1.01  smt_solver_calls:                       0
% 2.34/1.01  smt_fast_solver_calls:                  0
% 2.34/1.01  prop_num_of_clauses:                    1182
% 2.34/1.01  prop_preprocess_simplified:             4563
% 2.34/1.01  prop_fo_subsumed:                       29
% 2.34/1.01  prop_solver_time:                       0.
% 2.34/1.01  smt_solver_time:                        0.
% 2.34/1.01  smt_fast_solver_time:                   0.
% 2.34/1.01  prop_fast_solver_time:                  0.
% 2.34/1.01  prop_unsat_core_time:                   0.
% 2.34/1.01  
% 2.34/1.01  ------ QBF
% 2.34/1.01  
% 2.34/1.01  qbf_q_res:                              0
% 2.34/1.01  qbf_num_tautologies:                    0
% 2.34/1.01  qbf_prep_cycles:                        0
% 2.34/1.01  
% 2.34/1.01  ------ BMC1
% 2.34/1.01  
% 2.34/1.01  bmc1_current_bound:                     -1
% 2.34/1.01  bmc1_last_solved_bound:                 -1
% 2.34/1.01  bmc1_unsat_core_size:                   -1
% 2.34/1.01  bmc1_unsat_core_parents_size:           -1
% 2.34/1.01  bmc1_merge_next_fun:                    0
% 2.34/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation
% 2.34/1.01  
% 2.34/1.01  inst_num_of_clauses:                    436
% 2.34/1.01  inst_num_in_passive:                    154
% 2.34/1.01  inst_num_in_active:                     220
% 2.34/1.01  inst_num_in_unprocessed:                62
% 2.34/1.01  inst_num_of_loops:                      290
% 2.34/1.01  inst_num_of_learning_restarts:          0
% 2.34/1.01  inst_num_moves_active_passive:          65
% 2.34/1.01  inst_lit_activity:                      0
% 2.34/1.01  inst_lit_activity_moves:                0
% 2.34/1.01  inst_num_tautologies:                   0
% 2.34/1.01  inst_num_prop_implied:                  0
% 2.34/1.01  inst_num_existing_simplified:           0
% 2.34/1.01  inst_num_eq_res_simplified:             0
% 2.34/1.01  inst_num_child_elim:                    0
% 2.34/1.01  inst_num_of_dismatching_blockings:      81
% 2.34/1.01  inst_num_of_non_proper_insts:           400
% 2.34/1.01  inst_num_of_duplicates:                 0
% 2.34/1.01  inst_inst_num_from_inst_to_res:         0
% 2.34/1.01  inst_dismatching_checking_time:         0.
% 2.34/1.01  
% 2.34/1.01  ------ Resolution
% 2.34/1.01  
% 2.34/1.01  res_num_of_clauses:                     0
% 2.34/1.01  res_num_in_passive:                     0
% 2.34/1.01  res_num_in_active:                      0
% 2.34/1.01  res_num_of_loops:                       136
% 2.34/1.01  res_forward_subset_subsumed:            33
% 2.34/1.01  res_backward_subset_subsumed:           0
% 2.34/1.01  res_forward_subsumed:                   0
% 2.34/1.01  res_backward_subsumed:                  0
% 2.34/1.01  res_forward_subsumption_resolution:     0
% 2.34/1.01  res_backward_subsumption_resolution:    0
% 2.34/1.01  res_clause_to_clause_subsumption:       132
% 2.34/1.01  res_orphan_elimination:                 0
% 2.34/1.01  res_tautology_del:                      44
% 2.34/1.01  res_num_eq_res_simplified:              0
% 2.34/1.01  res_num_sel_changes:                    0
% 2.34/1.01  res_moves_from_active_to_pass:          0
% 2.34/1.01  
% 2.34/1.01  ------ Superposition
% 2.34/1.01  
% 2.34/1.01  sup_time_total:                         0.
% 2.34/1.01  sup_time_generating:                    0.
% 2.34/1.01  sup_time_sim_full:                      0.
% 2.34/1.01  sup_time_sim_immed:                     0.
% 2.34/1.01  
% 2.34/1.01  sup_num_of_clauses:                     53
% 2.34/1.01  sup_num_in_active:                      33
% 2.34/1.01  sup_num_in_passive:                     20
% 2.34/1.01  sup_num_of_loops:                       57
% 2.34/1.01  sup_fw_superposition:                   18
% 2.34/1.01  sup_bw_superposition:                   24
% 2.34/1.01  sup_immediate_simplified:               23
% 2.34/1.01  sup_given_eliminated:                   0
% 2.34/1.01  comparisons_done:                       0
% 2.34/1.01  comparisons_avoided:                    15
% 2.34/1.01  
% 2.34/1.01  ------ Simplifications
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  sim_fw_subset_subsumed:                 1
% 2.34/1.01  sim_bw_subset_subsumed:                 0
% 2.34/1.01  sim_fw_subsumed:                        1
% 2.34/1.01  sim_bw_subsumed:                        0
% 2.34/1.01  sim_fw_subsumption_res:                 0
% 2.34/1.01  sim_bw_subsumption_res:                 0
% 2.34/1.01  sim_tautology_del:                      0
% 2.34/1.01  sim_eq_tautology_del:                   0
% 2.34/1.01  sim_eq_res_simp:                        0
% 2.34/1.01  sim_fw_demodulated:                     6
% 2.34/1.01  sim_bw_demodulated:                     24
% 2.34/1.01  sim_light_normalised:                   33
% 2.34/1.01  sim_joinable_taut:                      0
% 2.34/1.01  sim_joinable_simp:                      0
% 2.34/1.01  sim_ac_normalised:                      0
% 2.34/1.01  sim_smt_subsumption:                    0
% 2.34/1.01  
%------------------------------------------------------------------------------
