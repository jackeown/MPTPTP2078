%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:46 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  306 (14203 expanded)
%              Number of clauses        :  168 (3898 expanded)
%              Number of leaves         :   40 (4725 expanded)
%              Depth                    :   34
%              Number of atoms          :  813 (93540 expanded)
%              Number of equality atoms :  361 (26664 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),sK4)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X3)
            & v2_funct_1(sK3)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k7_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X3) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2),X3)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK4)
    & v2_funct_1(sK3)
    & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f78,f90,f89,f88,f87])).

fof(f146,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f91])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f140,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f143,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f91])).

fof(f142,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f91])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f148,plain,(
    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f91])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f64])).

fof(f128,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f149,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

fof(f144,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f122,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f119,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f129,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f123,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f62])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f70])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f145,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f150,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f91])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f75])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f81])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f159,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f79])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f151,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f102,f103])).

fof(f152,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f101,f151])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f100,f152])).

fof(f154,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f99,f153])).

fof(f155,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f98,f154])).

fof(f156,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f97,f155])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f125,f156])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f121,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f85,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f43])).

fof(f130,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f85])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f160,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f105])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_41,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_50,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_597,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_50])).

cnf(c_598,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_51,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_602,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_51])).

cnf(c_603,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_2163,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2106,c_598,c_603])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2110,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3849,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2163,c_2110])).

cnf(c_45,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_2156,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_45,c_598,c_603])).

cnf(c_4036,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3849,c_2156])).

cnf(c_4042,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4036,c_2163])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2122,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4650,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4042,c_2122])).

cnf(c_56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2405,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2553,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2405])).

cnf(c_2554,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2689,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2690,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2689])).

cnf(c_5180,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4650,c_56,c_2554,c_2690])).

cnf(c_30,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_44,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_780,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_44])).

cnf(c_781,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_783,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_49])).

cnf(c_2103,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_5188,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5180,c_2103])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_826,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_44])).

cnf(c_827,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_829,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_49])).

cnf(c_2100,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_5190,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5180,c_2100])).

cnf(c_5196,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5188,c_5190])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_358,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_20,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_967,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_359,c_20])).

cnf(c_968,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_2095,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_5819,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k4_relat_1(sK3))))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_2095])).

cnf(c_29,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_794,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_44])).

cnf(c_795,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_797,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_49])).

cnf(c_2102,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_5189,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5180,c_2102])).

cnf(c_5193,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5189,c_5190])).

cnf(c_5830,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5819,c_5193])).

cnf(c_54,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2115,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5237,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5190,c_2115])).

cnf(c_7996,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5830,c_54,c_56,c_2554,c_2690,c_5237])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2108,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8005,plain,
    ( k8_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k4_relat_1(sK3),X0) = k10_relat_1(k4_relat_1(sK3),X0) ),
    inference(superposition,[status(thm)],[c_7996,c_2108])).

cnf(c_28,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_808,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_44])).

cnf(c_809,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_813,plain,
    ( ~ v1_relat_1(sK3)
    | k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_809,c_49])).

cnf(c_2101,plain,
    ( k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_5187,plain,
    ( k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_5180,c_2101])).

cnf(c_5199,plain,
    ( k10_relat_1(k4_relat_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_5187,c_5190])).

cnf(c_8016,plain,
    ( k8_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k4_relat_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_8005,c_5199])).

cnf(c_33,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_38,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_757,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_48])).

cnf(c_758,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_760,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_49,c_47])).

cnf(c_873,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_760])).

cnf(c_874,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_874])).

cnf(c_912,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_1446,plain,
    ( ~ v1_relat_1(sK3)
    | sP0_iProver_split
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_912])).

cnf(c_2097,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1446])).

cnf(c_2257,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2097,c_598,c_603])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_912])).

cnf(c_2098,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_2212,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2098,c_603])).

cnf(c_2637,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2163,c_2212])).

cnf(c_2649,plain,
    ( v1_relat_1(sK3) != iProver_top
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2257,c_2637])).

cnf(c_2650,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2649])).

cnf(c_4041,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4036,c_2650])).

cnf(c_4066,plain,
    ( ~ v1_relat_1(sK3)
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4041])).

cnf(c_4964,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4041,c_47,c_2553,c_2689,c_4066])).

cnf(c_4965,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4964])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2109,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5492,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_4042,c_2109])).

cnf(c_43,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_48])).

cnf(c_747,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_749,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_747,c_49,c_47,c_44])).

cnf(c_2266,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_749,c_598,c_603,c_2156])).

cnf(c_2267,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_2266])).

cnf(c_2294,plain,
    ( k8_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3),sK4) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_43,c_598,c_603,c_2267])).

cnf(c_4043,plain,
    ( k8_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3),sK4) != k7_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_4036,c_2294])).

cnf(c_5224,plain,
    ( k8_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k4_relat_1(sK3),sK4) != k7_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_5190,c_4043])).

cnf(c_6037,plain,
    ( k8_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k4_relat_1(sK3),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_5492,c_5224])).

cnf(c_6041,plain,
    ( k8_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k4_relat_1(sK3),sK4) != k9_relat_1(sK3,sK4)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4965,c_6037])).

cnf(c_8161,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8016,c_6041])).

cnf(c_8162,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8161])).

cnf(c_8179,plain,
    ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),k4_relat_1(sK3),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_8162,c_6037])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_356,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_356])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_951,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_357,c_4])).

cnf(c_2096,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_3247,plain,
    ( r1_xboole_0(sK3,k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2163,c_2096])).

cnf(c_4039,plain,
    ( r1_xboole_0(sK3,k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4036,c_3247])).

cnf(c_8184,plain,
    ( r1_xboole_0(sK3,k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8162,c_4039])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f159])).

cnf(c_8200,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8184,c_5])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2126,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_18,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f158])).

cnf(c_2113,plain,
    ( k10_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k1_xboole_0
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6756,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_2113])).

cnf(c_21,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_6767,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6756,c_21])).

cnf(c_32,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_89,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6844,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6767,c_89])).

cnf(c_6851,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_6844])).

cnf(c_8666,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8200,c_6851])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2128,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8672,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8666,c_2128])).

cnf(c_10090,plain,
    ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),k4_relat_1(k1_xboole_0),sK4) != k9_relat_1(k1_xboole_0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_8179,c_8672])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2124,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_33,c_19])).

cnf(c_2104,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_3780,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2124,c_2104])).

cnf(c_7876,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3780,c_89])).

cnf(c_2111,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2118,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3658,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2111,c_2118])).

cnf(c_7882,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7876,c_3658])).

cnf(c_7884,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7882,c_21])).

cnf(c_8166,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8162,c_7996])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f160])).

cnf(c_8241,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8166,c_6])).

cnf(c_4668,plain,
    ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k10_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2108])).

cnf(c_8621,plain,
    ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(sK3),X1) = k10_relat_1(k4_relat_1(sK3),X1) ),
    inference(superposition,[status(thm)],[c_8241,c_4668])).

cnf(c_8635,plain,
    ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(sK3),X1) = k9_relat_1(sK3,X1) ),
    inference(demodulation,[status(thm)],[c_8621,c_5199])).

cnf(c_9978,plain,
    ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(k1_xboole_0),X1) = k9_relat_1(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8635,c_8672])).

cnf(c_9979,plain,
    ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(k1_xboole_0),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9978,c_7884])).

cnf(c_10091,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10090,c_7884,c_9979])).

cnf(c_10092,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10091])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:38:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.32/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.98  
% 3.32/0.98  ------  iProver source info
% 3.32/0.98  
% 3.32/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.98  git: non_committed_changes: false
% 3.32/0.98  git: last_make_outside_of_git: false
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  
% 3.32/0.98  ------ Input Options
% 3.32/0.98  
% 3.32/0.98  --out_options                           all
% 3.32/0.98  --tptp_safe_out                         true
% 3.32/0.98  --problem_path                          ""
% 3.32/0.98  --include_path                          ""
% 3.32/0.98  --clausifier                            res/vclausify_rel
% 3.32/0.98  --clausifier_options                    --mode clausify
% 3.32/0.98  --stdin                                 false
% 3.32/0.98  --stats_out                             all
% 3.32/0.98  
% 3.32/0.98  ------ General Options
% 3.32/0.98  
% 3.32/0.98  --fof                                   false
% 3.32/0.98  --time_out_real                         305.
% 3.32/0.98  --time_out_virtual                      -1.
% 3.32/0.98  --symbol_type_check                     false
% 3.32/0.98  --clausify_out                          false
% 3.32/0.98  --sig_cnt_out                           false
% 3.32/0.98  --trig_cnt_out                          false
% 3.32/0.98  --trig_cnt_out_tolerance                1.
% 3.32/0.98  --trig_cnt_out_sk_spl                   false
% 3.32/0.98  --abstr_cl_out                          false
% 3.32/0.98  
% 3.32/0.98  ------ Global Options
% 3.32/0.98  
% 3.32/0.98  --schedule                              default
% 3.32/0.98  --add_important_lit                     false
% 3.32/0.98  --prop_solver_per_cl                    1000
% 3.32/0.98  --min_unsat_core                        false
% 3.32/0.98  --soft_assumptions                      false
% 3.32/0.98  --soft_lemma_size                       3
% 3.32/0.98  --prop_impl_unit_size                   0
% 3.32/0.98  --prop_impl_unit                        []
% 3.32/0.98  --share_sel_clauses                     true
% 3.32/0.98  --reset_solvers                         false
% 3.32/0.98  --bc_imp_inh                            [conj_cone]
% 3.32/0.98  --conj_cone_tolerance                   3.
% 3.32/0.98  --extra_neg_conj                        none
% 3.32/0.98  --large_theory_mode                     true
% 3.32/0.98  --prolific_symb_bound                   200
% 3.32/0.98  --lt_threshold                          2000
% 3.32/0.98  --clause_weak_htbl                      true
% 3.32/0.98  --gc_record_bc_elim                     false
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing Options
% 3.32/0.98  
% 3.32/0.98  --preprocessing_flag                    true
% 3.32/0.98  --time_out_prep_mult                    0.1
% 3.32/0.98  --splitting_mode                        input
% 3.32/0.98  --splitting_grd                         true
% 3.32/0.98  --splitting_cvd                         false
% 3.32/0.98  --splitting_cvd_svl                     false
% 3.32/0.98  --splitting_nvd                         32
% 3.32/0.98  --sub_typing                            true
% 3.32/0.98  --prep_gs_sim                           true
% 3.32/0.98  --prep_unflatten                        true
% 3.32/0.98  --prep_res_sim                          true
% 3.32/0.98  --prep_upred                            true
% 3.32/0.98  --prep_sem_filter                       exhaustive
% 3.32/0.98  --prep_sem_filter_out                   false
% 3.32/0.98  --pred_elim                             true
% 3.32/0.98  --res_sim_input                         true
% 3.32/0.98  --eq_ax_congr_red                       true
% 3.32/0.98  --pure_diseq_elim                       true
% 3.32/0.98  --brand_transform                       false
% 3.32/0.98  --non_eq_to_eq                          false
% 3.32/0.98  --prep_def_merge                        true
% 3.32/0.98  --prep_def_merge_prop_impl              false
% 3.32/0.98  --prep_def_merge_mbd                    true
% 3.32/0.98  --prep_def_merge_tr_red                 false
% 3.32/0.98  --prep_def_merge_tr_cl                  false
% 3.32/0.98  --smt_preprocessing                     true
% 3.32/0.98  --smt_ac_axioms                         fast
% 3.32/0.98  --preprocessed_out                      false
% 3.32/0.98  --preprocessed_stats                    false
% 3.32/0.98  
% 3.32/0.98  ------ Abstraction refinement Options
% 3.32/0.98  
% 3.32/0.98  --abstr_ref                             []
% 3.32/0.98  --abstr_ref_prep                        false
% 3.32/0.98  --abstr_ref_until_sat                   false
% 3.32/0.98  --abstr_ref_sig_restrict                funpre
% 3.32/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.98  --abstr_ref_under                       []
% 3.32/0.98  
% 3.32/0.98  ------ SAT Options
% 3.32/0.98  
% 3.32/0.98  --sat_mode                              false
% 3.32/0.98  --sat_fm_restart_options                ""
% 3.32/0.98  --sat_gr_def                            false
% 3.32/0.98  --sat_epr_types                         true
% 3.32/0.98  --sat_non_cyclic_types                  false
% 3.32/0.98  --sat_finite_models                     false
% 3.32/0.98  --sat_fm_lemmas                         false
% 3.32/0.98  --sat_fm_prep                           false
% 3.32/0.98  --sat_fm_uc_incr                        true
% 3.32/0.98  --sat_out_model                         small
% 3.32/0.98  --sat_out_clauses                       false
% 3.32/0.98  
% 3.32/0.98  ------ QBF Options
% 3.32/0.98  
% 3.32/0.98  --qbf_mode                              false
% 3.32/0.98  --qbf_elim_univ                         false
% 3.32/0.98  --qbf_dom_inst                          none
% 3.32/0.98  --qbf_dom_pre_inst                      false
% 3.32/0.98  --qbf_sk_in                             false
% 3.32/0.98  --qbf_pred_elim                         true
% 3.32/0.98  --qbf_split                             512
% 3.32/0.98  
% 3.32/0.98  ------ BMC1 Options
% 3.32/0.98  
% 3.32/0.98  --bmc1_incremental                      false
% 3.32/0.98  --bmc1_axioms                           reachable_all
% 3.32/0.98  --bmc1_min_bound                        0
% 3.32/0.98  --bmc1_max_bound                        -1
% 3.32/0.98  --bmc1_max_bound_default                -1
% 3.32/0.98  --bmc1_symbol_reachability              true
% 3.32/0.98  --bmc1_property_lemmas                  false
% 3.32/0.98  --bmc1_k_induction                      false
% 3.32/0.98  --bmc1_non_equiv_states                 false
% 3.32/0.98  --bmc1_deadlock                         false
% 3.32/0.98  --bmc1_ucm                              false
% 3.32/0.98  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     num_symb
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       true
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  ------ Parsing...
% 3.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.99  ------ Proving...
% 3.32/0.99  ------ Problem Properties 
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  clauses                                 46
% 3.32/0.99  conjectures                             5
% 3.32/0.99  EPR                                     5
% 3.32/0.99  Horn                                    41
% 3.32/0.99  unary                                   16
% 3.32/0.99  binary                                  17
% 3.32/0.99  lits                                    91
% 3.32/0.99  lits eq                                 31
% 3.32/0.99  fd_pure                                 0
% 3.32/0.99  fd_pseudo                               0
% 3.32/0.99  fd_cond                                 2
% 3.32/0.99  fd_pseudo_cond                          0
% 3.32/0.99  AC symbols                              0
% 3.32/0.99  
% 3.32/0.99  ------ Schedule dynamic 5 is on 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  Current options:
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     none
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       false
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ Proving...
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS status Theorem for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99   Resolution empty clause
% 3.32/0.99  
% 3.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  fof(f38,conjecture,(
% 3.32/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f39,negated_conjecture,(
% 3.32/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 3.32/0.99    inference(negated_conjecture,[],[f38])).
% 3.32/0.99  
% 3.32/0.99  fof(f77,plain,(
% 3.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f39])).
% 3.32/0.99  
% 3.32/0.99  fof(f78,plain,(
% 3.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 3.32/0.99    inference(flattening,[],[f77])).
% 3.32/0.99  
% 3.32/0.99  fof(f90,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),sK4) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f89,plain,(
% 3.32/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f88,plain,(
% 3.32/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X3) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f87,plain,(
% 3.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f91,plain,(
% 3.32/0.99    (((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK4) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f78,f90,f89,f88,f87])).
% 3.32/0.99  
% 3.32/0.99  fof(f146,plain,(
% 3.32/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f36,axiom,(
% 3.32/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f74,plain,(
% 3.32/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f140,plain,(
% 3.32/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f74])).
% 3.32/0.99  
% 3.32/0.99  fof(f143,plain,(
% 3.32/0.99    l1_struct_0(sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f142,plain,(
% 3.32/0.99    l1_struct_0(sK1)),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f31,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f67,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f133,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f67])).
% 3.32/0.99  
% 3.32/0.99  fof(f148,plain,(
% 3.32/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f15,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f50,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f15])).
% 3.32/0.99  
% 3.32/0.99  fof(f111,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f17,axiom,(
% 3.32/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f114,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f17])).
% 3.32/0.99  
% 3.32/0.99  fof(f28,axiom,(
% 3.32/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f64,plain,(
% 3.32/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f28])).
% 3.32/0.99  
% 3.32/0.99  fof(f65,plain,(
% 3.32/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(flattening,[],[f64])).
% 3.32/0.99  
% 3.32/0.99  fof(f128,plain,(
% 3.32/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f65])).
% 3.32/0.99  
% 3.32/0.99  fof(f149,plain,(
% 3.32/0.99    v2_funct_1(sK3)),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f144,plain,(
% 3.32/0.99    v1_funct_1(sK3)),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f24,axiom,(
% 3.32/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f57,plain,(
% 3.32/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f58,plain,(
% 3.32/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(flattening,[],[f57])).
% 3.32/0.99  
% 3.32/0.99  fof(f122,plain,(
% 3.32/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f58])).
% 3.32/0.99  
% 3.32/0.99  fof(f13,axiom,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f83,plain,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.32/0.99    inference(nnf_transformation,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f109,plain,(
% 3.32/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f83])).
% 3.32/0.99  
% 3.32/0.99  fof(f22,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f56,plain,(
% 3.32/0.99    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f22])).
% 3.32/0.99  
% 3.32/0.99  fof(f119,plain,(
% 3.32/0.99    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f56])).
% 3.32/0.99  
% 3.32/0.99  fof(f129,plain,(
% 3.32/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f65])).
% 3.32/0.99  
% 3.32/0.99  fof(f25,axiom,(
% 3.32/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f59,plain,(
% 3.32/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f60,plain,(
% 3.32/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(flattening,[],[f59])).
% 3.32/0.99  
% 3.32/0.99  fof(f123,plain,(
% 3.32/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f60])).
% 3.32/0.99  
% 3.32/0.99  fof(f33,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f69,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f33])).
% 3.32/0.99  
% 3.32/0.99  fof(f135,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f69])).
% 3.32/0.99  
% 3.32/0.99  fof(f27,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f62,plain,(
% 3.32/0.99    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f27])).
% 3.32/0.99  
% 3.32/0.99  fof(f63,plain,(
% 3.32/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f62])).
% 3.32/0.99  
% 3.32/0.99  fof(f127,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f63])).
% 3.32/0.99  
% 3.32/0.99  fof(f30,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f42,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.32/0.99    inference(pure_predicate_removal,[],[f30])).
% 3.32/0.99  
% 3.32/0.99  fof(f66,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f42])).
% 3.32/0.99  
% 3.32/0.99  fof(f132,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f66])).
% 3.32/0.99  
% 3.32/0.99  fof(f34,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f70,plain,(
% 3.32/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f34])).
% 3.32/0.99  
% 3.32/0.99  fof(f71,plain,(
% 3.32/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f70])).
% 3.32/0.99  
% 3.32/0.99  fof(f86,plain,(
% 3.32/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f71])).
% 3.32/0.99  
% 3.32/0.99  fof(f136,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f86])).
% 3.32/0.99  
% 3.32/0.99  fof(f35,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f72,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f73,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.32/0.99    inference(flattening,[],[f72])).
% 3.32/0.99  
% 3.32/0.99  fof(f138,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f73])).
% 3.32/0.99  
% 3.32/0.99  fof(f145,plain,(
% 3.32/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f32,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f68,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f134,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f68])).
% 3.32/0.99  
% 3.32/0.99  fof(f150,plain,(
% 3.32/0.99    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK4)),
% 3.32/0.99    inference(cnf_transformation,[],[f91])).
% 3.32/0.99  
% 3.32/0.99  fof(f37,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f75,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f37])).
% 3.32/0.99  
% 3.32/0.99  fof(f76,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.32/0.99    inference(flattening,[],[f75])).
% 3.32/0.99  
% 3.32/0.99  fof(f141,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f76])).
% 3.32/0.99  
% 3.32/0.99  fof(f108,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f83])).
% 3.32/0.99  
% 3.32/0.99  fof(f3,axiom,(
% 3.32/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f3])).
% 3.32/0.99  
% 3.32/0.99  fof(f47,plain,(
% 3.32/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.32/0.99    inference(flattening,[],[f46])).
% 3.32/0.99  
% 3.32/0.99  fof(f96,plain,(
% 3.32/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f47])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f81,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.32/0.99    inference(nnf_transformation,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f82,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.32/0.99    inference(flattening,[],[f81])).
% 3.32/0.99  
% 3.32/0.99  fof(f106,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.32/0.99    inference(cnf_transformation,[],[f82])).
% 3.32/0.99  
% 3.32/0.99  fof(f159,plain,(
% 3.32/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.32/0.99    inference(equality_resolution,[],[f106])).
% 3.32/0.99  
% 3.32/0.99  fof(f2,axiom,(
% 3.32/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f40,plain,(
% 3.32/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.99    inference(rectify,[],[f2])).
% 3.32/0.99  
% 3.32/0.99  fof(f45,plain,(
% 3.32/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f79,plain,(
% 3.32/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f80,plain,(
% 3.32/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f79])).
% 3.32/0.99  
% 3.32/0.99  fof(f94,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f80])).
% 3.32/0.99  
% 3.32/0.99  fof(f20,axiom,(
% 3.32/0.99    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f117,plain,(
% 3.32/0.99    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f20])).
% 3.32/0.99  
% 3.32/0.99  fof(f26,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f61,plain,(
% 3.32/0.99    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f26])).
% 3.32/0.99  
% 3.32/0.99  fof(f84,plain,(
% 3.32/0.99    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f61])).
% 3.32/0.99  
% 3.32/0.99  fof(f125,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f84])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f97,plain,(
% 3.32/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f4])).
% 3.32/0.99  
% 3.32/0.99  fof(f5,axiom,(
% 3.32/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f98,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f5])).
% 3.32/0.99  
% 3.32/0.99  fof(f6,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f99,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f6])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f100,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f8,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f101,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f8])).
% 3.32/0.99  
% 3.32/0.99  fof(f9,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f102,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f9])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f103,plain,(
% 3.32/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f151,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f102,f103])).
% 3.32/0.99  
% 3.32/0.99  fof(f152,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f101,f151])).
% 3.32/0.99  
% 3.32/0.99  fof(f153,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f100,f152])).
% 3.32/0.99  
% 3.32/0.99  fof(f154,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f99,f153])).
% 3.32/0.99  
% 3.32/0.99  fof(f155,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f98,f154])).
% 3.32/0.99  
% 3.32/0.99  fof(f156,plain,(
% 3.32/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f97,f155])).
% 3.32/0.99  
% 3.32/0.99  fof(f158,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f125,f156])).
% 3.32/0.99  
% 3.32/0.99  fof(f23,axiom,(
% 3.32/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f121,plain,(
% 3.32/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.32/0.99    inference(cnf_transformation,[],[f23])).
% 3.32/0.99  
% 3.32/0.99  fof(f29,axiom,(
% 3.32/0.99    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f41,plain,(
% 3.32/0.99    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 3.32/0.99    inference(pure_predicate_removal,[],[f29])).
% 3.32/0.99  
% 3.32/0.99  fof(f43,plain,(
% 3.32/0.99    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 3.32/0.99    inference(pure_predicate_removal,[],[f41])).
% 3.32/0.99  
% 3.32/0.99  fof(f85,plain,(
% 3.32/0.99    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 3.32/0.99    inference(rectify,[],[f43])).
% 3.32/0.99  
% 3.32/0.99  fof(f130,plain,(
% 3.32/0.99    v1_relat_1(k1_xboole_0)),
% 3.32/0.99    inference(cnf_transformation,[],[f85])).
% 3.32/0.99  
% 3.32/0.99  fof(f1,axiom,(
% 3.32/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f44,plain,(
% 3.32/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f1])).
% 3.32/0.99  
% 3.32/0.99  fof(f92,plain,(
% 3.32/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f44])).
% 3.32/0.99  
% 3.32/0.99  fof(f12,axiom,(
% 3.32/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f107,plain,(
% 3.32/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f12])).
% 3.32/0.99  
% 3.32/0.99  fof(f21,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f54,plain,(
% 3.32/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f21])).
% 3.32/0.99  
% 3.32/0.99  fof(f55,plain,(
% 3.32/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f54])).
% 3.32/0.99  
% 3.32/0.99  fof(f118,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f18,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f52,plain,(
% 3.32/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f18])).
% 3.32/0.99  
% 3.32/0.99  fof(f115,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f52])).
% 3.32/0.99  
% 3.32/0.99  fof(f105,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.32/0.99    inference(cnf_transformation,[],[f82])).
% 3.32/0.99  
% 3.32/0.99  fof(f160,plain,(
% 3.32/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.32/0.99    inference(equality_resolution,[],[f105])).
% 3.32/0.99  
% 3.32/0.99  cnf(c_47,negated_conjecture,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f146]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2106,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_41,plain,
% 3.32/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f140]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_50,negated_conjecture,
% 3.32/0.99      ( l1_struct_0(sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f143]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_597,plain,
% 3.32/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_41,c_50]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_598,plain,
% 3.32/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_597]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_51,negated_conjecture,
% 3.32/0.99      ( l1_struct_0(sK1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f142]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_602,plain,
% 3.32/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_41,c_51]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_603,plain,
% 3.32/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_602]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2163,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_2106,c_598,c_603]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_34,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f133]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2110,plain,
% 3.32/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3849,plain,
% 3.32/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2163,c_2110]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_45,negated_conjecture,
% 3.32/0.99      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f148]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2156,plain,
% 3.32/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_45,c_598,c_603]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4036,plain,
% 3.32/0.99      ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_3849,c_2156]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4042,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4036,c_2163]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2122,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/0.99      | v1_relat_1(X1) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4650,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))) != iProver_top
% 3.32/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4042,c_2122]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_56,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2405,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | v1_relat_1(sK3) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2553,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.32/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 3.32/0.99      | v1_relat_1(sK3) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_2405]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2554,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.32/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
% 3.32/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2553]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_15,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2689,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2690,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2689]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5180,plain,
% 3.32/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4650,c_56,c_2554,c_2690]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_30,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v2_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_44,negated_conjecture,
% 3.32/0.99      ( v2_funct_1(sK3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f149]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_780,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_44]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_781,plain,
% 3.32/0.99      ( ~ v1_funct_1(sK3)
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_780]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_49,negated_conjecture,
% 3.32/0.99      ( v1_funct_1(sK3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f144]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_783,plain,
% 3.32/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_781,c_49]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2103,plain,
% 3.32/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5188,plain,
% 3.32/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5180,c_2103]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_23,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v2_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_826,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_44]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_827,plain,
% 3.32/0.99      ( ~ v1_funct_1(sK3)
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_826]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_829,plain,
% 3.32/0.99      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_827,c_49]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2100,plain,
% 3.32/0.99      ( k2_funct_1(sK3) = k4_relat_1(sK3) | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5190,plain,
% 3.32/0.99      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5180,c_2100]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5196,plain,
% 3.32/0.99      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5188,c_5190]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_358,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.32/0.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_359,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_358]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_20,plain,
% 3.32/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_967,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/0.99      | ~ v1_relat_1(X2)
% 3.32/0.99      | X2 != X0
% 3.32/0.99      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_359,c_20]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_968,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_967]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2095,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5819,plain,
% 3.32/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k4_relat_1(sK3))))) = iProver_top
% 3.32/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5196,c_2095]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_29,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v2_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f129]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_794,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_44]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_795,plain,
% 3.32/0.99      ( ~ v1_funct_1(sK3)
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_794]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_797,plain,
% 3.32/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_795,c_49]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2102,plain,
% 3.32/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5189,plain,
% 3.32/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5180,c_2102]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5193,plain,
% 3.32/0.99      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5189,c_5190]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5830,plain,
% 3.32/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
% 3.32/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5819,c_5193]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_54,plain,
% 3.32/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_25,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2115,plain,
% 3.32/0.99      ( v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5237,plain,
% 3.32/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.32/0.99      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5190,c_2115]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7996,plain,
% 3.32/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_5830,c_54,c_56,c_2554,c_2690,c_5237]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_36,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f135]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2108,plain,
% 3.32/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8005,plain,
% 3.32/0.99      ( k8_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k4_relat_1(sK3),X0) = k10_relat_1(k4_relat_1(sK3),X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_7996,c_2108]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_28,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v2_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_808,plain,
% 3.32/0.99      ( ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_44]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_809,plain,
% 3.32/0.99      ( ~ v1_funct_1(sK3)
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_808]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_813,plain,
% 3.32/0.99      ( ~ v1_relat_1(sK3)
% 3.32/0.99      | k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_809,c_49]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2101,plain,
% 3.32/0.99      ( k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0)
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5187,plain,
% 3.32/0.99      ( k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5180,c_2101]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5199,plain,
% 3.32/0.99      ( k10_relat_1(k4_relat_1(sK3),X0) = k9_relat_1(sK3,X0) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5187,c_5190]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8016,plain,
% 3.32/0.99      ( k8_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k4_relat_1(sK3),X0) = k9_relat_1(sK3,X0) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_8005,c_5199]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_33,plain,
% 3.32/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f132]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_38,plain,
% 3.32/0.99      ( ~ v1_partfun1(X0,X1)
% 3.32/0.99      | ~ v4_relat_1(X0,X1)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k1_relat_1(X0) = X1 ),
% 3.32/0.99      inference(cnf_transformation,[],[f136]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_40,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | v1_partfun1(X0,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f138]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_48,negated_conjecture,
% 3.32/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f145]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_757,plain,
% 3.32/0.99      ( v1_partfun1(X0,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | u1_struct_0(sK2) != X2
% 3.32/0.99      | u1_struct_0(sK1) != X1
% 3.32/0.99      | sK3 != X0
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_40,c_48]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_758,plain,
% 3.32/0.99      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 3.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.32/0.99      | ~ v1_funct_1(sK3)
% 3.32/0.99      | k1_xboole_0 = u1_struct_0(sK2) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_757]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_760,plain,
% 3.32/0.99      ( v1_partfun1(sK3,u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK2) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_758,c_49,c_47]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_873,plain,
% 3.32/0.99      ( ~ v4_relat_1(X0,X1)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | u1_struct_0(sK1) != X1
% 3.32/0.99      | k1_relat_1(X0) = X1
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_38,c_760]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_874,plain,
% 3.32/0.99      ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_873]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_911,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | u1_struct_0(sK1) != X1
% 3.32/0.99      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_874]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_912,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
% 3.32/0.99      | ~ v1_relat_1(sK3)
% 3.32/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_911]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1446,plain,
% 3.32/0.99      ( ~ v1_relat_1(sK3)
% 3.32/0.99      | sP0_iProver_split
% 3.32/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(splitting,
% 3.32/0.99                [splitting(split),new_symbols(definition,[])],
% 3.32/0.99                [c_912]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2097,plain,
% 3.32/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top
% 3.32/0.99      | sP0_iProver_split = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1446]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2257,plain,
% 3.32/0.99      ( k2_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top
% 3.32/0.99      | sP0_iProver_split = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_2097,c_598,c_603]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1445,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
% 3.32/0.99      | ~ sP0_iProver_split ),
% 3.32/0.99      inference(splitting,
% 3.32/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.32/0.99                [c_912]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2098,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))) != iProver_top
% 3.32/0.99      | sP0_iProver_split != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1445]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2212,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0))) != iProver_top
% 3.32/0.99      | sP0_iProver_split != iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_2098,c_603]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2637,plain,
% 3.32/0.99      ( sP0_iProver_split != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2163,c_2212]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2649,plain,
% 3.32/0.99      ( v1_relat_1(sK3) != iProver_top
% 3.32/0.99      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | k2_struct_0(sK2) = k1_xboole_0 ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2257,c_2637]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2650,plain,
% 3.32/0.99      ( k2_struct_0(sK2) = k1_xboole_0
% 3.32/0.99      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_2649]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4041,plain,
% 3.32/0.99      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 3.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4036,c_2650]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4066,plain,
% 3.32/0.99      ( ~ v1_relat_1(sK3)
% 3.32/0.99      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 3.32/0.99      | k2_relat_1(sK3) = k1_xboole_0 ),
% 3.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4041]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4964,plain,
% 3.32/0.99      ( k2_relat_1(sK3) = k1_xboole_0 | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4041,c_47,c_2553,c_2689,c_4066]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4965,plain,
% 3.32/0.99      ( k2_struct_0(sK1) = k1_relat_1(sK3) | k2_relat_1(sK3) = k1_xboole_0 ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_4964]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_35,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f134]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2109,plain,
% 3.32/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5492,plain,
% 3.32/0.99      ( k7_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4042,c_2109]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_43,negated_conjecture,
% 3.32/0.99      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK4) ),
% 3.32/0.99      inference(cnf_transformation,[],[f150]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_42,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v2_funct_1(X0)
% 3.32/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.32/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f141]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_746,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v2_funct_1(X0)
% 3.32/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.32/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.32/0.99      | u1_struct_0(sK2) != X2
% 3.32/0.99      | u1_struct_0(sK1) != X1
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_42,c_48]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_747,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.32/0.99      | ~ v1_funct_1(sK3)
% 3.32/0.99      | ~ v2_funct_1(sK3)
% 3.32/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
% 3.32/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_746]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_749,plain,
% 3.32/0.99      ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
% 3.32/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_747,c_49,c_47,c_44]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2266,plain,
% 3.32/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3)
% 3.32/0.99      | k2_struct_0(sK2) != k2_struct_0(sK2) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_749,c_598,c_603,c_2156]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2267,plain,
% 3.32/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
% 3.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_2266]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2294,plain,
% 3.32/0.99      ( k8_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_funct_1(sK3),sK4) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_43,c_598,c_603,c_2267]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4043,plain,
% 3.32/0.99      ( k8_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3),sK4) != k7_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3,sK4) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4036,c_2294]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5224,plain,
% 3.32/0.99      ( k8_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k4_relat_1(sK3),sK4) != k7_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3,sK4) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5190,c_4043]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6037,plain,
% 3.32/0.99      ( k8_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k4_relat_1(sK3),sK4) != k9_relat_1(sK3,sK4) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5492,c_5224]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6041,plain,
% 3.32/0.99      ( k8_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k4_relat_1(sK3),sK4) != k9_relat_1(sK3,sK4)
% 3.32/0.99      | k2_relat_1(sK3) = k1_xboole_0 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4965,c_6037]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8161,plain,
% 3.32/0.99      ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4)
% 3.32/0.99      | k2_relat_1(sK3) = k1_xboole_0 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8016,c_6041]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8162,plain,
% 3.32/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_8161]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8179,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),k4_relat_1(sK3),sK4) != k9_relat_1(sK3,sK4) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8162,c_6037]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_10,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_356,plain,
% 3.32/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.32/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_357,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_356]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_951,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/0.99      | ~ r1_xboole_0(X0,X1)
% 3.32/0.99      | v1_xboole_0(X0) ),
% 3.32/0.99      inference(resolution,[status(thm)],[c_357,c_4]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2096,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/0.99      | r1_xboole_0(X0,X1) != iProver_top
% 3.32/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3247,plain,
% 3.32/0.99      ( r1_xboole_0(sK3,k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != iProver_top
% 3.32/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2163,c_2096]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4039,plain,
% 3.32/0.99      ( r1_xboole_0(sK3,k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))) != iProver_top
% 3.32/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4036,c_3247]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8184,plain,
% 3.32/0.99      ( r1_xboole_0(sK3,k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)) != iProver_top
% 3.32/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8162,c_4039]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5,plain,
% 3.32/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f159]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8200,plain,
% 3.32/0.99      ( r1_xboole_0(sK3,k1_xboole_0) != iProver_top
% 3.32/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8184,c_5]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2,plain,
% 3.32/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2126,plain,
% 3.32/0.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.32/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_18,plain,
% 3.32/0.99      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_27,plain,
% 3.32/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | k10_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f158]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2113,plain,
% 3.32/0.99      ( k10_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k1_xboole_0
% 3.32/0.99      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6756,plain,
% 3.32/0.99      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 3.32/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_18,c_2113]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_21,plain,
% 3.32/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6767,plain,
% 3.32/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.32/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_6756,c_21]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_32,plain,
% 3.32/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f130]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_89,plain,
% 3.32/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6844,plain,
% 3.32/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6767,c_89]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6851,plain,
% 3.32/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2126,c_6844]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8666,plain,
% 3.32/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 3.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_8200,c_6851]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_0,plain,
% 3.32/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2128,plain,
% 3.32/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8672,plain,
% 3.32/0.99      ( sK3 = k1_xboole_0 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_8666,c_2128]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_10090,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,k2_struct_0(sK1),k4_relat_1(k1_xboole_0),sK4) != k9_relat_1(k1_xboole_0,sK4) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_8179,c_8672]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8,plain,
% 3.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2124,plain,
% 3.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_19,plain,
% 3.32/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_899,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.32/0.99      inference(resolution,[status(thm)],[c_33,c_19]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2104,plain,
% 3.32/0.99      ( k7_relat_1(X0,X1) = X0
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3780,plain,
% 3.32/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.32/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2124,c_2104]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7876,plain,
% 3.32/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3780,c_89]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2111,plain,
% 3.32/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_16,plain,
% 3.32/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2118,plain,
% 3.32/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3658,plain,
% 3.32/0.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2111,c_2118]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7882,plain,
% 3.32/0.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_7876,c_3658]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7884,plain,
% 3.32/0.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_7882,c_21]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8166,plain,
% 3.32/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8162,c_7996]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6,plain,
% 3.32/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f160]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8241,plain,
% 3.32/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8166,c_6]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4668,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k10_relat_1(X1,X2)
% 3.32/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_6,c_2108]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8621,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(sK3),X1) = k10_relat_1(k4_relat_1(sK3),X1) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_8241,c_4668]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8635,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(sK3),X1) = k9_relat_1(sK3,X1) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_8621,c_5199]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9978,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(k1_xboole_0),X1) = k9_relat_1(k1_xboole_0,X1) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_8635,c_8672]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9979,plain,
% 3.32/0.99      ( k8_relset_1(k1_xboole_0,X0,k4_relat_1(k1_xboole_0),X1) = k1_xboole_0 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_9978,c_7884]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_10091,plain,
% 3.32/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_10090,c_7884,c_9979]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_10092,plain,
% 3.32/0.99      ( $false ),
% 3.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_10091]) ).
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  ------                               Statistics
% 3.32/0.99  
% 3.32/0.99  ------ General
% 3.32/0.99  
% 3.32/0.99  abstr_ref_over_cycles:                  0
% 3.32/0.99  abstr_ref_under_cycles:                 0
% 3.32/0.99  gc_basic_clause_elim:                   0
% 3.32/0.99  forced_gc_time:                         0
% 3.32/0.99  parsing_time:                           0.01
% 3.32/0.99  unif_index_cands_time:                  0.
% 3.32/0.99  unif_index_add_time:                    0.
% 3.32/0.99  orderings_time:                         0.
% 3.32/0.99  out_proof_time:                         0.014
% 3.32/0.99  total_time:                             0.292
% 3.32/0.99  num_of_symbols:                         66
% 3.32/0.99  num_of_terms:                           9131
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing
% 3.32/0.99  
% 3.32/0.99  num_of_splits:                          1
% 3.32/0.99  num_of_split_atoms:                     1
% 3.32/0.99  num_of_reused_defs:                     0
% 3.32/0.99  num_eq_ax_congr_red:                    49
% 3.32/0.99  num_of_sem_filtered_clauses:            1
% 3.32/0.99  num_of_subtypes:                        0
% 3.32/0.99  monotx_restored_types:                  0
% 3.32/0.99  sat_num_of_epr_types:                   0
% 3.32/0.99  sat_num_of_non_cyclic_types:            0
% 3.32/0.99  sat_guarded_non_collapsed_types:        0
% 3.32/0.99  num_pure_diseq_elim:                    0
% 3.32/0.99  simp_replaced_by:                       0
% 3.32/0.99  res_preprocessed:                       234
% 3.32/0.99  prep_upred:                             0
% 3.32/0.99  prep_unflattend:                        50
% 3.32/0.99  smt_new_axioms:                         0
% 3.32/0.99  pred_elim_cands:                        6
% 3.32/0.99  pred_elim:                              6
% 3.32/0.99  pred_elim_cl:                           7
% 3.32/0.99  pred_elim_cycles:                       10
% 3.32/0.99  merged_defs:                            2
% 3.32/0.99  merged_defs_ncl:                        0
% 3.32/0.99  bin_hyper_res:                          3
% 3.32/0.99  prep_cycles:                            4
% 3.32/0.99  pred_elim_time:                         0.011
% 3.32/0.99  splitting_time:                         0.
% 3.32/0.99  sem_filter_time:                        0.
% 3.32/0.99  monotx_time:                            0.
% 3.32/0.99  subtype_inf_time:                       0.
% 3.32/0.99  
% 3.32/0.99  ------ Problem properties
% 3.32/0.99  
% 3.32/0.99  clauses:                                46
% 3.32/0.99  conjectures:                            5
% 3.32/0.99  epr:                                    5
% 3.32/0.99  horn:                                   41
% 3.32/0.99  ground:                                 17
% 3.32/0.99  unary:                                  16
% 3.32/0.99  binary:                                 17
% 3.32/0.99  lits:                                   91
% 3.32/0.99  lits_eq:                                31
% 3.32/0.99  fd_pure:                                0
% 3.32/0.99  fd_pseudo:                              0
% 3.32/0.99  fd_cond:                                2
% 3.32/0.99  fd_pseudo_cond:                         0
% 3.32/0.99  ac_symbols:                             0
% 3.32/0.99  
% 3.32/0.99  ------ Propositional Solver
% 3.32/0.99  
% 3.32/0.99  prop_solver_calls:                      31
% 3.32/0.99  prop_fast_solver_calls:                 1462
% 3.32/0.99  smt_solver_calls:                       0
% 3.32/0.99  smt_fast_solver_calls:                  0
% 3.32/0.99  prop_num_of_clauses:                    3782
% 3.32/0.99  prop_preprocess_simplified:             10876
% 3.32/0.99  prop_fo_subsumed:                       33
% 3.32/0.99  prop_solver_time:                       0.
% 3.32/0.99  smt_solver_time:                        0.
% 3.32/0.99  smt_fast_solver_time:                   0.
% 3.32/0.99  prop_fast_solver_time:                  0.
% 3.32/0.99  prop_unsat_core_time:                   0.
% 3.32/0.99  
% 3.32/0.99  ------ QBF
% 3.32/0.99  
% 3.32/0.99  qbf_q_res:                              0
% 3.32/0.99  qbf_num_tautologies:                    0
% 3.32/0.99  qbf_prep_cycles:                        0
% 3.32/0.99  
% 3.32/0.99  ------ BMC1
% 3.32/0.99  
% 3.32/0.99  bmc1_current_bound:                     -1
% 3.32/0.99  bmc1_last_solved_bound:                 -1
% 3.32/0.99  bmc1_unsat_core_size:                   -1
% 3.32/0.99  bmc1_unsat_core_parents_size:           -1
% 3.32/0.99  bmc1_merge_next_fun:                    0
% 3.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation
% 3.32/0.99  
% 3.32/0.99  inst_num_of_clauses:                    1640
% 3.32/0.99  inst_num_in_passive:                    533
% 3.32/0.99  inst_num_in_active:                     647
% 3.32/0.99  inst_num_in_unprocessed:                460
% 3.32/0.99  inst_num_of_loops:                      750
% 3.32/0.99  inst_num_of_learning_restarts:          0
% 3.32/0.99  inst_num_moves_active_passive:          98
% 3.32/0.99  inst_lit_activity:                      0
% 3.32/0.99  inst_lit_activity_moves:                0
% 3.32/0.99  inst_num_tautologies:                   0
% 3.32/0.99  inst_num_prop_implied:                  0
% 3.32/0.99  inst_num_existing_simplified:           0
% 3.32/0.99  inst_num_eq_res_simplified:             0
% 3.32/0.99  inst_num_child_elim:                    0
% 3.32/0.99  inst_num_of_dismatching_blockings:      379
% 3.32/0.99  inst_num_of_non_proper_insts:           1106
% 3.32/0.99  inst_num_of_duplicates:                 0
% 3.32/0.99  inst_inst_num_from_inst_to_res:         0
% 3.32/0.99  inst_dismatching_checking_time:         0.
% 3.32/0.99  
% 3.32/0.99  ------ Resolution
% 3.32/0.99  
% 3.32/0.99  res_num_of_clauses:                     0
% 3.32/0.99  res_num_in_passive:                     0
% 3.32/0.99  res_num_in_active:                      0
% 3.32/0.99  res_num_of_loops:                       238
% 3.32/0.99  res_forward_subset_subsumed:            48
% 3.32/0.99  res_backward_subset_subsumed:           4
% 3.32/0.99  res_forward_subsumed:                   0
% 3.32/0.99  res_backward_subsumed:                  0
% 3.32/0.99  res_forward_subsumption_resolution:     1
% 3.32/0.99  res_backward_subsumption_resolution:    0
% 3.32/0.99  res_clause_to_clause_subsumption:       390
% 3.32/0.99  res_orphan_elimination:                 0
% 3.32/0.99  res_tautology_del:                      163
% 3.32/0.99  res_num_eq_res_simplified:              0
% 3.32/0.99  res_num_sel_changes:                    0
% 3.32/0.99  res_moves_from_active_to_pass:          0
% 3.32/0.99  
% 3.32/0.99  ------ Superposition
% 3.32/0.99  
% 3.32/0.99  sup_time_total:                         0.
% 3.32/0.99  sup_time_generating:                    0.
% 3.32/0.99  sup_time_sim_full:                      0.
% 3.32/0.99  sup_time_sim_immed:                     0.
% 3.32/0.99  
% 3.32/0.99  sup_num_of_clauses:                     159
% 3.32/0.99  sup_num_in_active:                      69
% 3.32/0.99  sup_num_in_passive:                     90
% 3.32/0.99  sup_num_of_loops:                       148
% 3.32/0.99  sup_fw_superposition:                   102
% 3.32/0.99  sup_bw_superposition:                   114
% 3.32/0.99  sup_immediate_simplified:               93
% 3.32/0.99  sup_given_eliminated:                   2
% 3.32/0.99  comparisons_done:                       0
% 3.32/0.99  comparisons_avoided:                    9
% 3.32/0.99  
% 3.32/0.99  ------ Simplifications
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  sim_fw_subset_subsumed:                 26
% 3.32/0.99  sim_bw_subset_subsumed:                 8
% 3.32/0.99  sim_fw_subsumed:                        17
% 3.32/0.99  sim_bw_subsumed:                        3
% 3.32/0.99  sim_fw_subsumption_res:                 1
% 3.32/0.99  sim_bw_subsumption_res:                 0
% 3.32/0.99  sim_tautology_del:                      3
% 3.32/0.99  sim_eq_tautology_del:                   8
% 3.32/0.99  sim_eq_res_simp:                        2
% 3.32/0.99  sim_fw_demodulated:                     30
% 3.32/0.99  sim_bw_demodulated:                     72
% 3.32/0.99  sim_light_normalised:                   59
% 3.32/0.99  sim_joinable_taut:                      0
% 3.32/0.99  sim_joinable_simp:                      0
% 3.32/0.99  sim_ac_normalised:                      0
% 3.32/0.99  sim_smt_subsumption:                    0
% 3.32/0.99  
%------------------------------------------------------------------------------
