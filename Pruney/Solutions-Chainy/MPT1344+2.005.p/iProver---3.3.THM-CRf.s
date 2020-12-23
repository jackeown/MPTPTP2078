%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:48 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  188 (1614 expanded)
%              Number of clauses        :  132 ( 525 expanded)
%              Number of leaves         :   20 ( 516 expanded)
%              Depth                    :   23
%              Number of atoms          :  674 (10802 expanded)
%              Number of equality atoms :  322 (3147 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),sK3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3)
            & v2_funct_1(sK2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f35,f34,f33,f32])).

fof(f52,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_250,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_738,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_264,plain,
    ( ~ l1_struct_0(X0_49)
    | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_726,plain,
    ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
    | l1_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_1151,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_738,c_726])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_251,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_737,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_1150,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_737,c_726])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_256,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1222,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1150,c_256])).

cnf(c_1332,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1151,c_1222])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_263,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_tops_2(X1_50,X2_50,X0_50) = k2_funct_1(X0_50)
    | k2_relset_1(X1_50,X2_50,X0_50) != X2_50 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_727,plain,
    ( k2_tops_2(X0_50,X1_50,X2_50) = k2_funct_1(X2_50)
    | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v2_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_2136,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_727])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_253,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_735,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_1219,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1150,c_735])).

cnf(c_1369,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1219,c_1151])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_254,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_734,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_1218,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1150,c_734])).

cnf(c_1428,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1218,c_1151])).

cnf(c_2418,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2136,c_26,c_30,c_1369,c_1428])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_262,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | m1_subset_1(k2_tops_2(X1_50,X2_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_728,plain,
    ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(k2_tops_2(X1_50,X2_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_2422,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2418,c_728])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_267,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X1_50,X2_50,X0_50) != X2_50 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_723,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(k2_funct_1(X2_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) = iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v2_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_1947,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_723])).

cnf(c_3458,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2422,c_26,c_30,c_1369,c_1428,c_1947])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k7_relset_1(X1_50,X2_50,X0_50,X3_50) = k9_relat_1(X0_50,X3_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_721,plain,
    ( k7_relset_1(X0_50,X1_50,X2_50,X3_50) = k9_relat_1(X2_50,X3_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_3467,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0_50) = k9_relat_1(k2_funct_1(sK2),X0_50) ),
    inference(superposition,[status(thm)],[c_3458,c_721])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k8_relset_1(X1_50,X2_50,X0_50,X3_50) = k10_relat_1(X0_50,X3_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_722,plain,
    ( k8_relset_1(X0_50,X1_50,X2_50,X3_50) = k10_relat_1(X2_50,X3_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_1507,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0_50) = k10_relat_1(sK2,X0_50) ),
    inference(superposition,[status(thm)],[c_1428,c_722])).

cnf(c_15,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_258,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1221,plain,
    ( k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1150,c_258])).

cnf(c_1331,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1151,c_1221])).

cnf(c_2421,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_2418,c_1331])).

cnf(c_2472,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1507,c_2421])).

cnf(c_3547,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_3467,c_2472])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_259,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_731,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(X1_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_2564,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_731])).

cnf(c_2591,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2564,c_1150])).

cnf(c_25,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3097,plain,
    ( l1_struct_0(X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_25])).

cnf(c_3098,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3097])).

cnf(c_3109,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_3098])).

cnf(c_3117,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3109,c_1151])).

cnf(c_24,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3238,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3117,c_24])).

cnf(c_3239,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3238])).

cnf(c_3250,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_3239])).

cnf(c_3251,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3250,c_2418])).

cnf(c_27,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_284,plain,
    ( X0_50 != X1_50
    | k2_funct_1(X0_50) = k2_funct_1(X1_50) ),
    theory(equality)).

cnf(c_297,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_275,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_307,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_336,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1005,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_1012,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_1013,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_278,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1059,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_50
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_50 ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_1241,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_1528,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X1_50 ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_2081,plain,
    ( X0_50 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | X0_50 != k2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_2415,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_286,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1583,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0_50 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_2971,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_2972,plain,
    ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2971])).

cnf(c_3701,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3251,c_24,c_22,c_25,c_21,c_26,c_20,c_27,c_19,c_28,c_16,c_30,c_297,c_307,c_336,c_256,c_1005,c_1013,c_1241,c_2415,c_2972])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_265,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50))
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X1_50,X2_50,X0_50) != X2_50 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_725,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(k2_funct_1(X2_50)) = iProver_top
    | v2_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_2054,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_725])).

cnf(c_996,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_997,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_2139,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2054,c_22,c_26,c_27,c_28,c_30,c_336,c_256,c_997,c_1241])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_271,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k10_relat_1(k2_funct_1(X0_50),X1_50) = k9_relat_1(X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_719,plain,
    ( k10_relat_1(k2_funct_1(X0_50),X1_50) = k9_relat_1(X0_50,X1_50)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_2145,plain,
    ( k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X0_50) = k9_relat_1(k2_funct_1(sK2),X0_50)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_719])).

cnf(c_252,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_736,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_270,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_720,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_1514,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_720])).

cnf(c_318,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_1082,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_272,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1132,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1682,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1514,c_21,c_19,c_16,c_318,c_1082,c_1132])).

cnf(c_2149,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2145,c_1682])).

cnf(c_1002,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_1003,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_1236,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1237,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_1490,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_2298,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2149,c_22,c_26,c_27,c_28,c_30,c_336,c_256,c_1003,c_1237,c_1241,c_1490])).

cnf(c_2299,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2298])).

cnf(c_3706,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50) ),
    inference(superposition,[status(thm)],[c_3701,c_2299])).

cnf(c_3797,plain,
    ( k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_3547,c_3706])).

cnf(c_3798,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3797])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.41/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/0.98  
% 2.41/0.98  ------  iProver source info
% 2.41/0.98  
% 2.41/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.41/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/0.98  git: non_committed_changes: false
% 2.41/0.98  git: last_make_outside_of_git: false
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options
% 2.41/0.98  
% 2.41/0.98  --out_options                           all
% 2.41/0.98  --tptp_safe_out                         true
% 2.41/0.98  --problem_path                          ""
% 2.41/0.98  --include_path                          ""
% 2.41/0.98  --clausifier                            res/vclausify_rel
% 2.41/0.98  --clausifier_options                    --mode clausify
% 2.41/0.98  --stdin                                 false
% 2.41/0.98  --stats_out                             all
% 2.41/0.98  
% 2.41/0.98  ------ General Options
% 2.41/0.98  
% 2.41/0.98  --fof                                   false
% 2.41/0.98  --time_out_real                         305.
% 2.41/0.98  --time_out_virtual                      -1.
% 2.41/0.98  --symbol_type_check                     false
% 2.41/0.98  --clausify_out                          false
% 2.41/0.98  --sig_cnt_out                           false
% 2.41/0.98  --trig_cnt_out                          false
% 2.41/0.98  --trig_cnt_out_tolerance                1.
% 2.41/0.98  --trig_cnt_out_sk_spl                   false
% 2.41/0.98  --abstr_cl_out                          false
% 2.41/0.98  
% 2.41/0.98  ------ Global Options
% 2.41/0.98  
% 2.41/0.98  --schedule                              default
% 2.41/0.98  --add_important_lit                     false
% 2.41/0.98  --prop_solver_per_cl                    1000
% 2.41/0.98  --min_unsat_core                        false
% 2.41/0.98  --soft_assumptions                      false
% 2.41/0.98  --soft_lemma_size                       3
% 2.41/0.98  --prop_impl_unit_size                   0
% 2.41/0.98  --prop_impl_unit                        []
% 2.41/0.98  --share_sel_clauses                     true
% 2.41/0.98  --reset_solvers                         false
% 2.41/0.98  --bc_imp_inh                            [conj_cone]
% 2.41/0.98  --conj_cone_tolerance                   3.
% 2.41/0.98  --extra_neg_conj                        none
% 2.41/0.98  --large_theory_mode                     true
% 2.41/0.98  --prolific_symb_bound                   200
% 2.41/0.98  --lt_threshold                          2000
% 2.41/0.98  --clause_weak_htbl                      true
% 2.41/0.98  --gc_record_bc_elim                     false
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing Options
% 2.41/0.98  
% 2.41/0.98  --preprocessing_flag                    true
% 2.41/0.98  --time_out_prep_mult                    0.1
% 2.41/0.98  --splitting_mode                        input
% 2.41/0.98  --splitting_grd                         true
% 2.41/0.98  --splitting_cvd                         false
% 2.41/0.98  --splitting_cvd_svl                     false
% 2.41/0.98  --splitting_nvd                         32
% 2.41/0.98  --sub_typing                            true
% 2.41/0.98  --prep_gs_sim                           true
% 2.41/0.98  --prep_unflatten                        true
% 2.41/0.98  --prep_res_sim                          true
% 2.41/0.98  --prep_upred                            true
% 2.41/0.98  --prep_sem_filter                       exhaustive
% 2.41/0.98  --prep_sem_filter_out                   false
% 2.41/0.98  --pred_elim                             true
% 2.41/0.98  --res_sim_input                         true
% 2.41/0.98  --eq_ax_congr_red                       true
% 2.41/0.98  --pure_diseq_elim                       true
% 2.41/0.98  --brand_transform                       false
% 2.41/0.98  --non_eq_to_eq                          false
% 2.41/0.98  --prep_def_merge                        true
% 2.41/0.98  --prep_def_merge_prop_impl              false
% 2.41/0.98  --prep_def_merge_mbd                    true
% 2.41/0.98  --prep_def_merge_tr_red                 false
% 2.41/0.98  --prep_def_merge_tr_cl                  false
% 2.41/0.98  --smt_preprocessing                     true
% 2.41/0.98  --smt_ac_axioms                         fast
% 2.41/0.98  --preprocessed_out                      false
% 2.41/0.98  --preprocessed_stats                    false
% 2.41/0.98  
% 2.41/0.98  ------ Abstraction refinement Options
% 2.41/0.98  
% 2.41/0.98  --abstr_ref                             []
% 2.41/0.98  --abstr_ref_prep                        false
% 2.41/0.98  --abstr_ref_until_sat                   false
% 2.41/0.98  --abstr_ref_sig_restrict                funpre
% 2.41/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.98  --abstr_ref_under                       []
% 2.41/0.98  
% 2.41/0.98  ------ SAT Options
% 2.41/0.98  
% 2.41/0.98  --sat_mode                              false
% 2.41/0.98  --sat_fm_restart_options                ""
% 2.41/0.98  --sat_gr_def                            false
% 2.41/0.98  --sat_epr_types                         true
% 2.41/0.98  --sat_non_cyclic_types                  false
% 2.41/0.98  --sat_finite_models                     false
% 2.41/0.98  --sat_fm_lemmas                         false
% 2.41/0.98  --sat_fm_prep                           false
% 2.41/0.98  --sat_fm_uc_incr                        true
% 2.41/0.98  --sat_out_model                         small
% 2.41/0.98  --sat_out_clauses                       false
% 2.41/0.98  
% 2.41/0.98  ------ QBF Options
% 2.41/0.98  
% 2.41/0.98  --qbf_mode                              false
% 2.41/0.98  --qbf_elim_univ                         false
% 2.41/0.98  --qbf_dom_inst                          none
% 2.41/0.98  --qbf_dom_pre_inst                      false
% 2.41/0.98  --qbf_sk_in                             false
% 2.41/0.98  --qbf_pred_elim                         true
% 2.41/0.98  --qbf_split                             512
% 2.41/0.98  
% 2.41/0.98  ------ BMC1 Options
% 2.41/0.98  
% 2.41/0.98  --bmc1_incremental                      false
% 2.41/0.98  --bmc1_axioms                           reachable_all
% 2.41/0.98  --bmc1_min_bound                        0
% 2.41/0.98  --bmc1_max_bound                        -1
% 2.41/0.98  --bmc1_max_bound_default                -1
% 2.41/0.98  --bmc1_symbol_reachability              true
% 2.41/0.98  --bmc1_property_lemmas                  false
% 2.41/0.98  --bmc1_k_induction                      false
% 2.41/0.98  --bmc1_non_equiv_states                 false
% 2.41/0.98  --bmc1_deadlock                         false
% 2.41/0.98  --bmc1_ucm                              false
% 2.41/0.98  --bmc1_add_unsat_core                   none
% 2.41/0.98  --bmc1_unsat_core_children              false
% 2.41/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.98  --bmc1_out_stat                         full
% 2.41/0.98  --bmc1_ground_init                      false
% 2.41/0.98  --bmc1_pre_inst_next_state              false
% 2.41/0.98  --bmc1_pre_inst_state                   false
% 2.41/0.98  --bmc1_pre_inst_reach_state             false
% 2.41/0.98  --bmc1_out_unsat_core                   false
% 2.41/0.98  --bmc1_aig_witness_out                  false
% 2.41/0.98  --bmc1_verbose                          false
% 2.41/0.98  --bmc1_dump_clauses_tptp                false
% 2.41/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.98  --bmc1_dump_file                        -
% 2.41/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.98  --bmc1_ucm_extend_mode                  1
% 2.41/0.98  --bmc1_ucm_init_mode                    2
% 2.41/0.98  --bmc1_ucm_cone_mode                    none
% 2.41/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.98  --bmc1_ucm_relax_model                  4
% 2.41/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.98  --bmc1_ucm_layered_model                none
% 2.41/0.98  --bmc1_ucm_max_lemma_size               10
% 2.41/0.98  
% 2.41/0.98  ------ AIG Options
% 2.41/0.98  
% 2.41/0.98  --aig_mode                              false
% 2.41/0.98  
% 2.41/0.98  ------ Instantiation Options
% 2.41/0.98  
% 2.41/0.98  --instantiation_flag                    true
% 2.41/0.98  --inst_sos_flag                         false
% 2.41/0.98  --inst_sos_phase                        true
% 2.41/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel_side                     num_symb
% 2.41/0.98  --inst_solver_per_active                1400
% 2.41/0.98  --inst_solver_calls_frac                1.
% 2.41/0.98  --inst_passive_queue_type               priority_queues
% 2.41/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.98  --inst_passive_queues_freq              [25;2]
% 2.41/0.98  --inst_dismatching                      true
% 2.41/0.98  --inst_eager_unprocessed_to_passive     true
% 2.41/0.98  --inst_prop_sim_given                   true
% 2.41/0.98  --inst_prop_sim_new                     false
% 2.41/0.98  --inst_subs_new                         false
% 2.41/0.98  --inst_eq_res_simp                      false
% 2.41/0.98  --inst_subs_given                       false
% 2.41/0.98  --inst_orphan_elimination               true
% 2.41/0.98  --inst_learning_loop_flag               true
% 2.41/0.98  --inst_learning_start                   3000
% 2.41/0.98  --inst_learning_factor                  2
% 2.41/0.98  --inst_start_prop_sim_after_learn       3
% 2.41/0.98  --inst_sel_renew                        solver
% 2.41/0.98  --inst_lit_activity_flag                true
% 2.41/0.98  --inst_restr_to_given                   false
% 2.41/0.98  --inst_activity_threshold               500
% 2.41/0.98  --inst_out_proof                        true
% 2.41/0.98  
% 2.41/0.98  ------ Resolution Options
% 2.41/0.98  
% 2.41/0.98  --resolution_flag                       true
% 2.41/0.98  --res_lit_sel                           adaptive
% 2.41/0.98  --res_lit_sel_side                      none
% 2.41/0.98  --res_ordering                          kbo
% 2.41/0.98  --res_to_prop_solver                    active
% 2.41/0.98  --res_prop_simpl_new                    false
% 2.41/0.98  --res_prop_simpl_given                  true
% 2.41/0.98  --res_passive_queue_type                priority_queues
% 2.41/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.98  --res_passive_queues_freq               [15;5]
% 2.41/0.98  --res_forward_subs                      full
% 2.41/0.98  --res_backward_subs                     full
% 2.41/0.98  --res_forward_subs_resolution           true
% 2.41/0.98  --res_backward_subs_resolution          true
% 2.41/0.98  --res_orphan_elimination                true
% 2.41/0.98  --res_time_limit                        2.
% 2.41/0.98  --res_out_proof                         true
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Options
% 2.41/0.98  
% 2.41/0.98  --superposition_flag                    true
% 2.41/0.98  --sup_passive_queue_type                priority_queues
% 2.41/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.98  --demod_completeness_check              fast
% 2.41/0.98  --demod_use_ground                      true
% 2.41/0.98  --sup_to_prop_solver                    passive
% 2.41/0.98  --sup_prop_simpl_new                    true
% 2.41/0.98  --sup_prop_simpl_given                  true
% 2.41/0.98  --sup_fun_splitting                     false
% 2.41/0.98  --sup_smt_interval                      50000
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Simplification Setup
% 2.41/0.98  
% 2.41/0.98  --sup_indices_passive                   []
% 2.41/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_full_bw                           [BwDemod]
% 2.41/0.98  --sup_immed_triv                        [TrivRules]
% 2.41/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_immed_bw_main                     []
% 2.41/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.98  
% 2.41/0.98  ------ Combination Options
% 2.41/0.98  
% 2.41/0.98  --comb_res_mult                         3
% 2.41/0.98  --comb_sup_mult                         2
% 2.41/0.98  --comb_inst_mult                        10
% 2.41/0.98  
% 2.41/0.98  ------ Debug Options
% 2.41/0.98  
% 2.41/0.98  --dbg_backtrace                         false
% 2.41/0.98  --dbg_dump_prop_clauses                 false
% 2.41/0.98  --dbg_dump_prop_clauses_file            -
% 2.41/0.98  --dbg_out_stat                          false
% 2.41/0.98  ------ Parsing...
% 2.41/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/0.98  ------ Proving...
% 2.41/0.98  ------ Problem Properties 
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  clauses                                 24
% 2.41/0.98  conjectures                             9
% 2.41/0.98  EPR                                     4
% 2.41/0.98  Horn                                    24
% 2.41/0.98  unary                                   10
% 2.41/0.98  binary                                  3
% 2.41/0.98  lits                                    71
% 2.41/0.98  lits eq                                 13
% 2.41/0.98  fd_pure                                 0
% 2.41/0.98  fd_pseudo                               0
% 2.41/0.98  fd_cond                                 0
% 2.41/0.98  fd_pseudo_cond                          0
% 2.41/0.98  AC symbols                              0
% 2.41/0.98  
% 2.41/0.98  ------ Schedule dynamic 5 is on 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  Current options:
% 2.41/0.98  ------ 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options
% 2.41/0.98  
% 2.41/0.98  --out_options                           all
% 2.41/0.98  --tptp_safe_out                         true
% 2.41/0.98  --problem_path                          ""
% 2.41/0.98  --include_path                          ""
% 2.41/0.98  --clausifier                            res/vclausify_rel
% 2.41/0.98  --clausifier_options                    --mode clausify
% 2.41/0.98  --stdin                                 false
% 2.41/0.98  --stats_out                             all
% 2.41/0.98  
% 2.41/0.98  ------ General Options
% 2.41/0.98  
% 2.41/0.98  --fof                                   false
% 2.41/0.98  --time_out_real                         305.
% 2.41/0.98  --time_out_virtual                      -1.
% 2.41/0.98  --symbol_type_check                     false
% 2.41/0.98  --clausify_out                          false
% 2.41/0.98  --sig_cnt_out                           false
% 2.41/0.98  --trig_cnt_out                          false
% 2.41/0.98  --trig_cnt_out_tolerance                1.
% 2.41/0.98  --trig_cnt_out_sk_spl                   false
% 2.41/0.98  --abstr_cl_out                          false
% 2.41/0.98  
% 2.41/0.98  ------ Global Options
% 2.41/0.98  
% 2.41/0.98  --schedule                              default
% 2.41/0.98  --add_important_lit                     false
% 2.41/0.98  --prop_solver_per_cl                    1000
% 2.41/0.98  --min_unsat_core                        false
% 2.41/0.98  --soft_assumptions                      false
% 2.41/0.98  --soft_lemma_size                       3
% 2.41/0.98  --prop_impl_unit_size                   0
% 2.41/0.98  --prop_impl_unit                        []
% 2.41/0.98  --share_sel_clauses                     true
% 2.41/0.98  --reset_solvers                         false
% 2.41/0.98  --bc_imp_inh                            [conj_cone]
% 2.41/0.98  --conj_cone_tolerance                   3.
% 2.41/0.98  --extra_neg_conj                        none
% 2.41/0.98  --large_theory_mode                     true
% 2.41/0.98  --prolific_symb_bound                   200
% 2.41/0.98  --lt_threshold                          2000
% 2.41/0.98  --clause_weak_htbl                      true
% 2.41/0.98  --gc_record_bc_elim                     false
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing Options
% 2.41/0.98  
% 2.41/0.98  --preprocessing_flag                    true
% 2.41/0.98  --time_out_prep_mult                    0.1
% 2.41/0.98  --splitting_mode                        input
% 2.41/0.98  --splitting_grd                         true
% 2.41/0.98  --splitting_cvd                         false
% 2.41/0.98  --splitting_cvd_svl                     false
% 2.41/0.98  --splitting_nvd                         32
% 2.41/0.98  --sub_typing                            true
% 2.41/0.98  --prep_gs_sim                           true
% 2.41/0.98  --prep_unflatten                        true
% 2.41/0.98  --prep_res_sim                          true
% 2.41/0.98  --prep_upred                            true
% 2.41/0.98  --prep_sem_filter                       exhaustive
% 2.41/0.98  --prep_sem_filter_out                   false
% 2.41/0.98  --pred_elim                             true
% 2.41/0.98  --res_sim_input                         true
% 2.41/0.98  --eq_ax_congr_red                       true
% 2.41/0.98  --pure_diseq_elim                       true
% 2.41/0.98  --brand_transform                       false
% 2.41/0.98  --non_eq_to_eq                          false
% 2.41/0.98  --prep_def_merge                        true
% 2.41/0.98  --prep_def_merge_prop_impl              false
% 2.41/0.98  --prep_def_merge_mbd                    true
% 2.41/0.98  --prep_def_merge_tr_red                 false
% 2.41/0.98  --prep_def_merge_tr_cl                  false
% 2.41/0.98  --smt_preprocessing                     true
% 2.41/0.98  --smt_ac_axioms                         fast
% 2.41/0.98  --preprocessed_out                      false
% 2.41/0.98  --preprocessed_stats                    false
% 2.41/0.98  
% 2.41/0.98  ------ Abstraction refinement Options
% 2.41/0.98  
% 2.41/0.98  --abstr_ref                             []
% 2.41/0.98  --abstr_ref_prep                        false
% 2.41/0.98  --abstr_ref_until_sat                   false
% 2.41/0.98  --abstr_ref_sig_restrict                funpre
% 2.41/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.98  --abstr_ref_under                       []
% 2.41/0.98  
% 2.41/0.98  ------ SAT Options
% 2.41/0.98  
% 2.41/0.98  --sat_mode                              false
% 2.41/0.98  --sat_fm_restart_options                ""
% 2.41/0.98  --sat_gr_def                            false
% 2.41/0.98  --sat_epr_types                         true
% 2.41/0.98  --sat_non_cyclic_types                  false
% 2.41/0.98  --sat_finite_models                     false
% 2.41/0.98  --sat_fm_lemmas                         false
% 2.41/0.98  --sat_fm_prep                           false
% 2.41/0.98  --sat_fm_uc_incr                        true
% 2.41/0.98  --sat_out_model                         small
% 2.41/0.98  --sat_out_clauses                       false
% 2.41/0.98  
% 2.41/0.98  ------ QBF Options
% 2.41/0.98  
% 2.41/0.98  --qbf_mode                              false
% 2.41/0.98  --qbf_elim_univ                         false
% 2.41/0.98  --qbf_dom_inst                          none
% 2.41/0.98  --qbf_dom_pre_inst                      false
% 2.41/0.98  --qbf_sk_in                             false
% 2.41/0.98  --qbf_pred_elim                         true
% 2.41/0.98  --qbf_split                             512
% 2.41/0.98  
% 2.41/0.98  ------ BMC1 Options
% 2.41/0.98  
% 2.41/0.98  --bmc1_incremental                      false
% 2.41/0.98  --bmc1_axioms                           reachable_all
% 2.41/0.98  --bmc1_min_bound                        0
% 2.41/0.98  --bmc1_max_bound                        -1
% 2.41/0.98  --bmc1_max_bound_default                -1
% 2.41/0.98  --bmc1_symbol_reachability              true
% 2.41/0.98  --bmc1_property_lemmas                  false
% 2.41/0.98  --bmc1_k_induction                      false
% 2.41/0.98  --bmc1_non_equiv_states                 false
% 2.41/0.98  --bmc1_deadlock                         false
% 2.41/0.98  --bmc1_ucm                              false
% 2.41/0.98  --bmc1_add_unsat_core                   none
% 2.41/0.98  --bmc1_unsat_core_children              false
% 2.41/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.98  --bmc1_out_stat                         full
% 2.41/0.98  --bmc1_ground_init                      false
% 2.41/0.98  --bmc1_pre_inst_next_state              false
% 2.41/0.98  --bmc1_pre_inst_state                   false
% 2.41/0.98  --bmc1_pre_inst_reach_state             false
% 2.41/0.98  --bmc1_out_unsat_core                   false
% 2.41/0.98  --bmc1_aig_witness_out                  false
% 2.41/0.98  --bmc1_verbose                          false
% 2.41/0.98  --bmc1_dump_clauses_tptp                false
% 2.41/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.98  --bmc1_dump_file                        -
% 2.41/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.98  --bmc1_ucm_extend_mode                  1
% 2.41/0.98  --bmc1_ucm_init_mode                    2
% 2.41/0.98  --bmc1_ucm_cone_mode                    none
% 2.41/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.98  --bmc1_ucm_relax_model                  4
% 2.41/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.98  --bmc1_ucm_layered_model                none
% 2.41/0.98  --bmc1_ucm_max_lemma_size               10
% 2.41/0.98  
% 2.41/0.98  ------ AIG Options
% 2.41/0.98  
% 2.41/0.98  --aig_mode                              false
% 2.41/0.98  
% 2.41/0.98  ------ Instantiation Options
% 2.41/0.98  
% 2.41/0.98  --instantiation_flag                    true
% 2.41/0.98  --inst_sos_flag                         false
% 2.41/0.98  --inst_sos_phase                        true
% 2.41/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel_side                     none
% 2.41/0.98  --inst_solver_per_active                1400
% 2.41/0.98  --inst_solver_calls_frac                1.
% 2.41/0.98  --inst_passive_queue_type               priority_queues
% 2.41/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.98  --inst_passive_queues_freq              [25;2]
% 2.41/0.98  --inst_dismatching                      true
% 2.41/0.98  --inst_eager_unprocessed_to_passive     true
% 2.41/0.98  --inst_prop_sim_given                   true
% 2.41/0.98  --inst_prop_sim_new                     false
% 2.41/0.98  --inst_subs_new                         false
% 2.41/0.98  --inst_eq_res_simp                      false
% 2.41/0.98  --inst_subs_given                       false
% 2.41/0.98  --inst_orphan_elimination               true
% 2.41/0.98  --inst_learning_loop_flag               true
% 2.41/0.98  --inst_learning_start                   3000
% 2.41/0.98  --inst_learning_factor                  2
% 2.41/0.98  --inst_start_prop_sim_after_learn       3
% 2.41/0.98  --inst_sel_renew                        solver
% 2.41/0.98  --inst_lit_activity_flag                true
% 2.41/0.98  --inst_restr_to_given                   false
% 2.41/0.98  --inst_activity_threshold               500
% 2.41/0.98  --inst_out_proof                        true
% 2.41/0.98  
% 2.41/0.98  ------ Resolution Options
% 2.41/0.98  
% 2.41/0.98  --resolution_flag                       false
% 2.41/0.98  --res_lit_sel                           adaptive
% 2.41/0.98  --res_lit_sel_side                      none
% 2.41/0.98  --res_ordering                          kbo
% 2.41/0.98  --res_to_prop_solver                    active
% 2.41/0.98  --res_prop_simpl_new                    false
% 2.41/0.98  --res_prop_simpl_given                  true
% 2.41/0.98  --res_passive_queue_type                priority_queues
% 2.41/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.98  --res_passive_queues_freq               [15;5]
% 2.41/0.98  --res_forward_subs                      full
% 2.41/0.98  --res_backward_subs                     full
% 2.41/0.98  --res_forward_subs_resolution           true
% 2.41/0.98  --res_backward_subs_resolution          true
% 2.41/0.98  --res_orphan_elimination                true
% 2.41/0.98  --res_time_limit                        2.
% 2.41/0.98  --res_out_proof                         true
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Options
% 2.41/0.98  
% 2.41/0.98  --superposition_flag                    true
% 2.41/0.98  --sup_passive_queue_type                priority_queues
% 2.41/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.98  --demod_completeness_check              fast
% 2.41/0.98  --demod_use_ground                      true
% 2.41/0.98  --sup_to_prop_solver                    passive
% 2.41/0.98  --sup_prop_simpl_new                    true
% 2.41/0.98  --sup_prop_simpl_given                  true
% 2.41/0.98  --sup_fun_splitting                     false
% 2.41/0.98  --sup_smt_interval                      50000
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Simplification Setup
% 2.41/0.98  
% 2.41/0.98  --sup_indices_passive                   []
% 2.41/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_full_bw                           [BwDemod]
% 2.41/0.98  --sup_immed_triv                        [TrivRules]
% 2.41/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_immed_bw_main                     []
% 2.41/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.98  
% 2.41/0.98  ------ Combination Options
% 2.41/0.98  
% 2.41/0.98  --comb_res_mult                         3
% 2.41/0.98  --comb_sup_mult                         2
% 2.41/0.98  --comb_inst_mult                        10
% 2.41/0.98  
% 2.41/0.98  ------ Debug Options
% 2.41/0.98  
% 2.41/0.98  --dbg_backtrace                         false
% 2.41/0.98  --dbg_dump_prop_clauses                 false
% 2.41/0.98  --dbg_dump_prop_clauses_file            -
% 2.41/0.98  --dbg_out_stat                          false
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  ------ Proving...
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  % SZS status Theorem for theBenchmark.p
% 2.41/0.98  
% 2.41/0.98   Resolution empty clause
% 2.41/0.98  
% 2.41/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  fof(f12,conjecture,(
% 2.41/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f13,negated_conjecture,(
% 2.41/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))),
% 2.41/0.98    inference(negated_conjecture,[],[f12])).
% 2.41/0.98  
% 2.41/0.98  fof(f30,plain,(
% 2.41/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.41/0.98    inference(ennf_transformation,[],[f13])).
% 2.41/0.98  
% 2.41/0.98  fof(f31,plain,(
% 2.41/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.41/0.98    inference(flattening,[],[f30])).
% 2.41/0.98  
% 2.41/0.98  fof(f35,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),sK3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.41/0.98    introduced(choice_axiom,[])).
% 2.41/0.98  
% 2.41/0.98  fof(f34,plain,(
% 2.41/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.41/0.98    introduced(choice_axiom,[])).
% 2.41/0.98  
% 2.41/0.98  fof(f33,plain,(
% 2.41/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.41/0.98    introduced(choice_axiom,[])).
% 2.41/0.98  
% 2.41/0.98  fof(f32,plain,(
% 2.41/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.41/0.98    introduced(choice_axiom,[])).
% 2.41/0.98  
% 2.41/0.98  fof(f36,plain,(
% 2.41/0.98    (((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.41/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f35,f34,f33,f32])).
% 2.41/0.98  
% 2.41/0.98  fof(f52,plain,(
% 2.41/0.98    l1_struct_0(sK0)),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f8,axiom,(
% 2.41/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f23,plain,(
% 2.41/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.41/0.98    inference(ennf_transformation,[],[f8])).
% 2.41/0.98  
% 2.41/0.98  fof(f46,plain,(
% 2.41/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f23])).
% 2.41/0.98  
% 2.41/0.98  fof(f53,plain,(
% 2.41/0.98    l1_struct_0(sK1)),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f58,plain,(
% 2.41/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f9,axiom,(
% 2.41/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f24,plain,(
% 2.41/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/0.98    inference(ennf_transformation,[],[f9])).
% 2.41/0.98  
% 2.41/0.98  fof(f25,plain,(
% 2.41/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/0.98    inference(flattening,[],[f24])).
% 2.41/0.98  
% 2.41/0.98  fof(f47,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f25])).
% 2.41/0.98  
% 2.41/0.98  fof(f54,plain,(
% 2.41/0.98    v1_funct_1(sK2)),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f59,plain,(
% 2.41/0.98    v2_funct_1(sK2)),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f55,plain,(
% 2.41/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f56,plain,(
% 2.41/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f10,axiom,(
% 2.41/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f26,plain,(
% 2.41/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/0.98    inference(ennf_transformation,[],[f10])).
% 2.41/0.98  
% 2.41/0.98  fof(f27,plain,(
% 2.41/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/0.98    inference(flattening,[],[f26])).
% 2.41/0.98  
% 2.41/0.98  fof(f50,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f27])).
% 2.41/0.98  
% 2.41/0.98  fof(f7,axiom,(
% 2.41/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f21,plain,(
% 2.41/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/0.98    inference(ennf_transformation,[],[f7])).
% 2.41/0.98  
% 2.41/0.98  fof(f22,plain,(
% 2.41/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/0.98    inference(flattening,[],[f21])).
% 2.41/0.98  
% 2.41/0.98  fof(f45,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f22])).
% 2.41/0.98  
% 2.41/0.98  fof(f5,axiom,(
% 2.41/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f19,plain,(
% 2.41/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.98    inference(ennf_transformation,[],[f5])).
% 2.41/0.98  
% 2.41/0.98  fof(f41,plain,(
% 2.41/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/0.98    inference(cnf_transformation,[],[f19])).
% 2.41/0.98  
% 2.41/0.98  fof(f6,axiom,(
% 2.41/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f20,plain,(
% 2.41/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.98    inference(ennf_transformation,[],[f6])).
% 2.41/0.98  
% 2.41/0.98  fof(f42,plain,(
% 2.41/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/0.98    inference(cnf_transformation,[],[f20])).
% 2.41/0.98  
% 2.41/0.98  fof(f60,plain,(
% 2.41/0.98    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),
% 2.41/0.98    inference(cnf_transformation,[],[f36])).
% 2.41/0.98  
% 2.41/0.98  fof(f11,axiom,(
% 2.41/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f28,plain,(
% 2.41/0.98    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.41/0.98    inference(ennf_transformation,[],[f11])).
% 2.41/0.98  
% 2.41/0.98  fof(f29,plain,(
% 2.41/0.98    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.41/0.98    inference(flattening,[],[f28])).
% 2.41/0.98  
% 2.41/0.98  fof(f51,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f29])).
% 2.41/0.98  
% 2.41/0.98  fof(f43,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f22])).
% 2.41/0.98  
% 2.41/0.98  fof(f3,axiom,(
% 2.41/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f15,plain,(
% 2.41/0.98    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.41/0.98    inference(ennf_transformation,[],[f3])).
% 2.41/0.98  
% 2.41/0.98  fof(f16,plain,(
% 2.41/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.41/0.98    inference(flattening,[],[f15])).
% 2.41/0.98  
% 2.41/0.98  fof(f39,plain,(
% 2.41/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f16])).
% 2.41/0.98  
% 2.41/0.98  fof(f4,axiom,(
% 2.41/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f17,plain,(
% 2.41/0.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/0.98    inference(ennf_transformation,[],[f4])).
% 2.41/0.98  
% 2.41/0.98  fof(f18,plain,(
% 2.41/0.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/0.98    inference(flattening,[],[f17])).
% 2.41/0.98  
% 2.41/0.98  fof(f40,plain,(
% 2.41/0.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f18])).
% 2.41/0.98  
% 2.41/0.98  fof(f1,axiom,(
% 2.41/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f14,plain,(
% 2.41/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.41/0.98    inference(ennf_transformation,[],[f1])).
% 2.41/0.98  
% 2.41/0.98  fof(f37,plain,(
% 2.41/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f14])).
% 2.41/0.98  
% 2.41/0.98  fof(f2,axiom,(
% 2.41/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.41/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f38,plain,(
% 2.41/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.41/0.98    inference(cnf_transformation,[],[f2])).
% 2.41/0.98  
% 2.41/0.98  cnf(c_23,negated_conjecture,
% 2.41/0.98      ( l1_struct_0(sK0) ),
% 2.41/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_250,negated_conjecture,
% 2.41/0.98      ( l1_struct_0(sK0) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_738,plain,
% 2.41/0.98      ( l1_struct_0(sK0) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_9,plain,
% 2.41/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.41/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_264,plain,
% 2.41/0.98      ( ~ l1_struct_0(X0_49) | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_726,plain,
% 2.41/0.98      ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
% 2.41/0.98      | l1_struct_0(X0_49) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1151,plain,
% 2.41/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_738,c_726]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_22,negated_conjecture,
% 2.41/0.98      ( l1_struct_0(sK1) ),
% 2.41/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_251,negated_conjecture,
% 2.41/0.98      ( l1_struct_0(sK1) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_737,plain,
% 2.41/0.98      ( l1_struct_0(sK1) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1150,plain,
% 2.41/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_737,c_726]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_17,negated_conjecture,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_256,negated_conjecture,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1222,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1150,c_256]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1332,plain,
% 2.41/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1151,c_1222]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_10,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/0.98      | ~ v1_funct_1(X0)
% 2.41/0.98      | ~ v2_funct_1(X0)
% 2.41/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.41/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_263,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.41/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | ~ v1_funct_1(X0_50)
% 2.41/0.98      | ~ v2_funct_1(X0_50)
% 2.41/0.98      | k2_tops_2(X1_50,X2_50,X0_50) = k2_funct_1(X0_50)
% 2.41/0.98      | k2_relset_1(X1_50,X2_50,X0_50) != X2_50 ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_727,plain,
% 2.41/0.98      ( k2_tops_2(X0_50,X1_50,X2_50) = k2_funct_1(X2_50)
% 2.41/0.98      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.41/0.98      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 2.41/0.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.41/0.98      | v1_funct_1(X2_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X2_50) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2136,plain,
% 2.41/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.41/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1332,c_727]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_21,negated_conjecture,
% 2.41/0.98      ( v1_funct_1(sK2) ),
% 2.41/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_26,plain,
% 2.41/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_16,negated_conjecture,
% 2.41/0.98      ( v2_funct_1(sK2) ),
% 2.41/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_30,plain,
% 2.41/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_20,negated_conjecture,
% 2.41/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.41/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_253,negated_conjecture,
% 2.41/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_735,plain,
% 2.41/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1219,plain,
% 2.41/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1150,c_735]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1369,plain,
% 2.41/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.41/0.98      inference(light_normalisation,[status(thm)],[c_1219,c_1151]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_19,negated_conjecture,
% 2.41/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.41/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_254,negated_conjecture,
% 2.41/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_734,plain,
% 2.41/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1218,plain,
% 2.41/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1150,c_734]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1428,plain,
% 2.41/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.41/0.98      inference(light_normalisation,[status(thm)],[c_1218,c_1151]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2418,plain,
% 2.41/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.41/0.98      inference(global_propositional_subsumption,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_2136,c_26,c_30,c_1369,c_1428]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_11,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/0.98      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/0.98      | ~ v1_funct_1(X0) ),
% 2.41/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_262,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.41/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | m1_subset_1(k2_tops_2(X1_50,X2_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 2.41/0.98      | ~ v1_funct_1(X0_50) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_728,plain,
% 2.41/0.98      ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 2.41/0.98      | m1_subset_1(k2_tops_2(X1_50,X2_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) = iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2422,plain,
% 2.41/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_2418,c_728]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_6,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/0.98      | ~ v1_funct_1(X0)
% 2.41/0.98      | ~ v2_funct_1(X0)
% 2.41/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_267,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.41/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 2.41/0.98      | ~ v1_funct_1(X0_50)
% 2.41/0.98      | ~ v2_funct_1(X0_50)
% 2.41/0.98      | k2_relset_1(X1_50,X2_50,X0_50) != X2_50 ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_723,plain,
% 2.41/0.98      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.41/0.98      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 2.41/0.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.41/0.98      | m1_subset_1(k2_funct_1(X2_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) = iProver_top
% 2.41/0.98      | v1_funct_1(X2_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X2_50) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1947,plain,
% 2.41/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1332,c_723]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3458,plain,
% 2.41/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.41/0.98      inference(global_propositional_subsumption,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_2422,c_26,c_30,c_1369,c_1428,c_1947]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_4,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.41/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_269,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | k7_relset_1(X1_50,X2_50,X0_50,X3_50) = k9_relat_1(X0_50,X3_50) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_721,plain,
% 2.41/0.98      ( k7_relset_1(X0_50,X1_50,X2_50,X3_50) = k9_relat_1(X2_50,X3_50)
% 2.41/0.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3467,plain,
% 2.41/0.98      ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0_50) = k9_relat_1(k2_funct_1(sK2),X0_50) ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_3458,c_721]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_5,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.41/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_268,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | k8_relset_1(X1_50,X2_50,X0_50,X3_50) = k10_relat_1(X0_50,X3_50) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_722,plain,
% 2.41/0.98      ( k8_relset_1(X0_50,X1_50,X2_50,X3_50) = k10_relat_1(X2_50,X3_50)
% 2.41/0.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1507,plain,
% 2.41/0.98      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0_50) = k10_relat_1(sK2,X0_50) ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1428,c_722]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_15,negated_conjecture,
% 2.41/0.98      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) ),
% 2.41/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_258,negated_conjecture,
% 2.41/0.98      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1221,plain,
% 2.41/0.98      ( k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1150,c_258]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1331,plain,
% 2.41/0.98      ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1151,c_1221]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2421,plain,
% 2.41/0.98      ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_2418,c_1331]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2472,plain,
% 2.41/0.98      ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_1507,c_2421]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3547,plain,
% 2.41/0.98      ( k9_relat_1(k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_3467,c_2472]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_14,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.41/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.41/0.98      | ~ l1_struct_0(X1)
% 2.41/0.98      | ~ l1_struct_0(X2)
% 2.41/0.98      | ~ v1_funct_1(X0)
% 2.41/0.98      | ~ v2_funct_1(X0)
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 2.41/0.98      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.41/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_259,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.41/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.41/0.98      | ~ l1_struct_0(X1_49)
% 2.41/0.98      | ~ l1_struct_0(X0_49)
% 2.41/0.98      | ~ v1_funct_1(X0_50)
% 2.41/0.98      | ~ v2_funct_1(X0_50)
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
% 2.41/0.98      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_731,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
% 2.41/0.98      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.41/0.98      | l1_struct_0(X0_49) != iProver_top
% 2.41/0.98      | l1_struct_0(X1_49) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2564,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | l1_struct_0(X0_49) != iProver_top
% 2.41/0.98      | l1_struct_0(sK1) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1150,c_731]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2591,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | l1_struct_0(X0_49) != iProver_top
% 2.41/0.98      | l1_struct_0(sK1) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(light_normalisation,[status(thm)],[c_2564,c_1150]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_25,plain,
% 2.41/0.98      ( l1_struct_0(sK1) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3097,plain,
% 2.41/0.98      ( l1_struct_0(X0_49) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2591,c_25]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3098,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | l1_struct_0(X0_49) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(renaming,[status(thm)],[c_3097]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3109,plain,
% 2.41/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(X0_50,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | l1_struct_0(sK0) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1151,c_3098]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3117,plain,
% 2.41/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | l1_struct_0(sK0) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(light_normalisation,[status(thm)],[c_3109,c_1151]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_24,plain,
% 2.41/0.98      ( l1_struct_0(sK0) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3238,plain,
% 2.41/0.98      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3117,c_24]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3239,plain,
% 2.41/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = iProver_top ),
% 2.41/0.98      inference(renaming,[status(thm)],[c_3238]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3250,plain,
% 2.41/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1332,c_3239]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3251,plain,
% 2.41/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(light_normalisation,[status(thm)],[c_3250,c_2418]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_27,plain,
% 2.41/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_28,plain,
% 2.41/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_284,plain,
% 2.41/0.98      ( X0_50 != X1_50 | k2_funct_1(X0_50) = k2_funct_1(X1_50) ),
% 2.41/0.98      theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_297,plain,
% 2.41/0.98      ( k2_funct_1(sK2) = k2_funct_1(sK2) | sK2 != sK2 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_284]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_275,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_307,plain,
% 2.41/0.98      ( sK2 = sK2 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_275]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_336,plain,
% 2.41/0.98      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_264]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1005,plain,
% 2.41/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/0.98      | ~ v1_funct_1(sK2)
% 2.41/0.98      | ~ v2_funct_1(sK2)
% 2.41/0.98      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.41/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_263]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1012,plain,
% 2.41/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/0.98      | ~ l1_struct_0(sK0)
% 2.41/0.98      | ~ l1_struct_0(sK1)
% 2.41/0.98      | ~ v1_funct_1(sK2)
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.41/0.98      | ~ v2_funct_1(sK2)
% 2.41/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_259]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1013,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | l1_struct_0(sK0) != iProver_top
% 2.41/0.98      | l1_struct_0(sK1) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_278,plain,
% 2.41/0.98      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.41/0.98      theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1059,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_50
% 2.41/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.41/0.98      | u1_struct_0(sK1) != X0_50 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_278]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1241,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.41/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.41/0.98      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_1059]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1528,plain,
% 2.41/0.98      ( X0_50 != X1_50
% 2.41/0.98      | X0_50 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 2.41/0.98      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X1_50 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_278]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2081,plain,
% 2.41/0.98      ( X0_50 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 2.41/0.98      | X0_50 != k2_funct_1(sK2)
% 2.41/0.98      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_1528]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2415,plain,
% 2.41/0.98      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 2.41/0.98      | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 2.41/0.98      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_2081]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_286,plain,
% 2.41/0.98      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 2.41/0.98      theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1583,plain,
% 2.41/0.98      ( ~ v2_funct_1(X0_50)
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2))
% 2.41/0.98      | k2_funct_1(sK2) != X0_50 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_286]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2971,plain,
% 2.41/0.98      ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2))
% 2.41/0.98      | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_1583]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2972,plain,
% 2.41/0.98      ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 2.41/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_2971]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3701,plain,
% 2.41/0.98      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.41/0.98      inference(global_propositional_subsumption,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_3251,c_24,c_22,c_25,c_21,c_26,c_20,c_27,c_19,c_28,c_16,
% 2.41/0.98                 c_30,c_297,c_307,c_336,c_256,c_1005,c_1013,c_1241,c_2415,
% 2.41/0.98                 c_2972]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_8,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/0.98      | ~ v1_funct_1(X0)
% 2.41/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.41/0.98      | ~ v2_funct_1(X0)
% 2.41/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_265,plain,
% 2.41/0.98      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.41/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | ~ v1_funct_1(X0_50)
% 2.41/0.98      | v1_funct_1(k2_funct_1(X0_50))
% 2.41/0.98      | ~ v2_funct_1(X0_50)
% 2.41/0.98      | k2_relset_1(X1_50,X2_50,X0_50) != X2_50 ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_725,plain,
% 2.41/0.98      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.41/0.98      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 2.41/0.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.41/0.98      | v1_funct_1(X2_50) != iProver_top
% 2.41/0.98      | v1_funct_1(k2_funct_1(X2_50)) = iProver_top
% 2.41/0.98      | v2_funct_1(X2_50) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2054,plain,
% 2.41/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_1332,c_725]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_996,plain,
% 2.41/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/0.98      | v1_funct_1(k2_funct_1(sK2))
% 2.41/0.98      | ~ v1_funct_1(sK2)
% 2.41/0.98      | ~ v2_funct_1(sK2)
% 2.41/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_265]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_997,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2139,plain,
% 2.41/0.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.41/0.98      inference(global_propositional_subsumption,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_2054,c_22,c_26,c_27,c_28,c_30,c_336,c_256,c_997,c_1241]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2,plain,
% 2.41/0.98      ( ~ v1_funct_1(X0)
% 2.41/0.98      | ~ v2_funct_1(X0)
% 2.41/0.98      | ~ v1_relat_1(X0)
% 2.41/0.98      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 2.41/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_271,plain,
% 2.41/0.98      ( ~ v1_funct_1(X0_50)
% 2.41/0.98      | ~ v2_funct_1(X0_50)
% 2.41/0.98      | ~ v1_relat_1(X0_50)
% 2.41/0.98      | k10_relat_1(k2_funct_1(X0_50),X1_50) = k9_relat_1(X0_50,X1_50) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_719,plain,
% 2.41/0.98      ( k10_relat_1(k2_funct_1(X0_50),X1_50) = k9_relat_1(X0_50,X1_50)
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v1_relat_1(X0_50) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2145,plain,
% 2.41/0.98      ( k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X0_50) = k9_relat_1(k2_funct_1(sK2),X0_50)
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.41/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_2139,c_719]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_252,negated_conjecture,
% 2.41/0.98      ( v1_funct_1(sK2) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_736,plain,
% 2.41/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3,plain,
% 2.41/0.98      ( ~ v1_funct_1(X0)
% 2.41/0.98      | ~ v2_funct_1(X0)
% 2.41/0.98      | ~ v1_relat_1(X0)
% 2.41/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.41/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_270,plain,
% 2.41/0.98      ( ~ v1_funct_1(X0_50)
% 2.41/0.98      | ~ v2_funct_1(X0_50)
% 2.41/0.98      | ~ v1_relat_1(X0_50)
% 2.41/0.98      | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_720,plain,
% 2.41/0.98      ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
% 2.41/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v2_funct_1(X0_50) != iProver_top
% 2.41/0.98      | v1_relat_1(X0_50) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1514,plain,
% 2.41/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top
% 2.41/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_736,c_720]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_318,plain,
% 2.41/0.98      ( ~ v1_funct_1(sK2)
% 2.41/0.98      | ~ v2_funct_1(sK2)
% 2.41/0.98      | ~ v1_relat_1(sK2)
% 2.41/0.98      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_270]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_0,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.41/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_273,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.41/0.98      | ~ v1_relat_1(X1_50)
% 2.41/0.98      | v1_relat_1(X0_50) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_932,plain,
% 2.41/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.41/0.98      | v1_relat_1(X0_50)
% 2.41/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_273]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1082,plain,
% 2.41/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/0.98      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.41/0.98      | v1_relat_1(sK2) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_932]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1,plain,
% 2.41/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.41/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_272,plain,
% 2.41/0.98      ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 2.41/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1132,plain,
% 2.41/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_272]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1682,plain,
% 2.41/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.41/0.98      inference(global_propositional_subsumption,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_1514,c_21,c_19,c_16,c_318,c_1082,c_1132]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2149,plain,
% 2.41/0.98      ( k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50)
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.41/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/0.98      inference(light_normalisation,[status(thm)],[c_2145,c_1682]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1002,plain,
% 2.41/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.41/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/0.98      | ~ v1_funct_1(sK2)
% 2.41/0.98      | ~ v2_funct_1(sK2)
% 2.41/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_267]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1003,plain,
% 2.41/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.41/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.41/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.41/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/0.98      | v1_funct_1(sK2) != iProver_top
% 2.41/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1236,plain,
% 2.41/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_272]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1237,plain,
% 2.41/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1479,plain,
% 2.41/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.41/0.98      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.41/0.98      | v1_relat_1(k2_funct_1(sK2)) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_932]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1490,plain,
% 2.41/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.41/0.98      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 2.41/0.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.41/0.98      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2298,plain,
% 2.41/0.98      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.41/0.98      | k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50) ),
% 2.41/0.98      inference(global_propositional_subsumption,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_2149,c_22,c_26,c_27,c_28,c_30,c_336,c_256,c_1003,c_1237,
% 2.41/0.98                 c_1241,c_1490]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2299,plain,
% 2.41/0.98      ( k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50)
% 2.41/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/0.98      inference(renaming,[status(thm)],[c_2298]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3706,plain,
% 2.41/0.98      ( k9_relat_1(k2_funct_1(sK2),X0_50) = k10_relat_1(sK2,X0_50) ),
% 2.41/0.98      inference(superposition,[status(thm)],[c_3701,c_2299]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3797,plain,
% 2.41/0.98      ( k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3) ),
% 2.41/0.98      inference(demodulation,[status(thm)],[c_3547,c_3706]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3798,plain,
% 2.41/0.98      ( $false ),
% 2.41/0.98      inference(equality_resolution_simp,[status(thm)],[c_3797]) ).
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  ------                               Statistics
% 2.41/0.98  
% 2.41/0.98  ------ General
% 2.41/0.98  
% 2.41/0.98  abstr_ref_over_cycles:                  0
% 2.41/0.98  abstr_ref_under_cycles:                 0
% 2.41/0.98  gc_basic_clause_elim:                   0
% 2.41/0.98  forced_gc_time:                         0
% 2.41/0.98  parsing_time:                           0.009
% 2.41/0.98  unif_index_cands_time:                  0.
% 2.41/0.98  unif_index_add_time:                    0.
% 2.41/0.98  orderings_time:                         0.
% 2.41/0.98  out_proof_time:                         0.012
% 2.41/0.98  total_time:                             0.184
% 2.41/0.98  num_of_symbols:                         56
% 2.41/0.98  num_of_terms:                           3652
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing
% 2.41/0.98  
% 2.41/0.98  num_of_splits:                          0
% 2.41/0.98  num_of_split_atoms:                     0
% 2.41/0.98  num_of_reused_defs:                     0
% 2.41/0.98  num_eq_ax_congr_red:                    9
% 2.41/0.98  num_of_sem_filtered_clauses:            1
% 2.41/0.98  num_of_subtypes:                        4
% 2.41/0.98  monotx_restored_types:                  0
% 2.41/0.98  sat_num_of_epr_types:                   0
% 2.41/0.98  sat_num_of_non_cyclic_types:            0
% 2.41/0.98  sat_guarded_non_collapsed_types:        1
% 2.41/0.98  num_pure_diseq_elim:                    0
% 2.41/0.98  simp_replaced_by:                       0
% 2.41/0.98  res_preprocessed:                       109
% 2.41/0.98  prep_upred:                             0
% 2.41/0.98  prep_unflattend:                        0
% 2.41/0.98  smt_new_axioms:                         0
% 2.41/0.98  pred_elim_cands:                        6
% 2.41/0.98  pred_elim:                              0
% 2.41/0.98  pred_elim_cl:                           0
% 2.41/0.98  pred_elim_cycles:                       1
% 2.41/0.98  merged_defs:                            0
% 2.41/0.98  merged_defs_ncl:                        0
% 2.41/0.98  bin_hyper_res:                          0
% 2.41/0.98  prep_cycles:                            3
% 2.41/0.98  pred_elim_time:                         0.
% 2.41/0.98  splitting_time:                         0.
% 2.41/0.98  sem_filter_time:                        0.
% 2.41/0.98  monotx_time:                            0.
% 2.41/0.98  subtype_inf_time:                       0.
% 2.41/0.98  
% 2.41/0.98  ------ Problem properties
% 2.41/0.98  
% 2.41/0.98  clauses:                                24
% 2.41/0.98  conjectures:                            9
% 2.41/0.98  epr:                                    4
% 2.41/0.98  horn:                                   24
% 2.41/0.98  ground:                                 9
% 2.41/0.98  unary:                                  10
% 2.41/0.98  binary:                                 3
% 2.41/0.98  lits:                                   71
% 2.41/0.98  lits_eq:                                13
% 2.41/0.98  fd_pure:                                0
% 2.41/0.98  fd_pseudo:                              0
% 2.41/0.98  fd_cond:                                0
% 2.41/0.98  fd_pseudo_cond:                         0
% 2.41/0.98  ac_symbols:                             0
% 2.41/0.98  
% 2.41/0.98  ------ Propositional Solver
% 2.41/0.98  
% 2.41/0.98  prop_solver_calls:                      24
% 2.41/0.98  prop_fast_solver_calls:                 945
% 2.41/0.98  smt_solver_calls:                       0
% 2.41/0.98  smt_fast_solver_calls:                  0
% 2.41/0.98  prop_num_of_clauses:                    1399
% 2.41/0.98  prop_preprocess_simplified:             4360
% 2.41/0.98  prop_fo_subsumed:                       46
% 2.41/0.98  prop_solver_time:                       0.
% 2.41/0.98  smt_solver_time:                        0.
% 2.41/0.98  smt_fast_solver_time:                   0.
% 2.41/0.98  prop_fast_solver_time:                  0.
% 2.41/0.98  prop_unsat_core_time:                   0.
% 2.41/0.98  
% 2.41/0.98  ------ QBF
% 2.41/0.98  
% 2.41/0.98  qbf_q_res:                              0
% 2.41/0.98  qbf_num_tautologies:                    0
% 2.41/0.98  qbf_prep_cycles:                        0
% 2.41/0.98  
% 2.41/0.98  ------ BMC1
% 2.41/0.98  
% 2.41/0.98  bmc1_current_bound:                     -1
% 2.41/0.98  bmc1_last_solved_bound:                 -1
% 2.41/0.98  bmc1_unsat_core_size:                   -1
% 2.41/0.98  bmc1_unsat_core_parents_size:           -1
% 2.41/0.98  bmc1_merge_next_fun:                    0
% 2.41/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.41/0.98  
% 2.41/0.98  ------ Instantiation
% 2.41/0.98  
% 2.41/0.98  inst_num_of_clauses:                    447
% 2.41/0.98  inst_num_in_passive:                    67
% 2.41/0.98  inst_num_in_active:                     306
% 2.41/0.98  inst_num_in_unprocessed:                74
% 2.41/0.98  inst_num_of_loops:                      330
% 2.41/0.98  inst_num_of_learning_restarts:          0
% 2.41/0.98  inst_num_moves_active_passive:          21
% 2.41/0.98  inst_lit_activity:                      0
% 2.41/0.98  inst_lit_activity_moves:                0
% 2.41/0.98  inst_num_tautologies:                   0
% 2.41/0.98  inst_num_prop_implied:                  0
% 2.41/0.98  inst_num_existing_simplified:           0
% 2.41/0.98  inst_num_eq_res_simplified:             0
% 2.41/0.98  inst_num_child_elim:                    0
% 2.41/0.98  inst_num_of_dismatching_blockings:      79
% 2.41/0.98  inst_num_of_non_proper_insts:           409
% 2.41/0.98  inst_num_of_duplicates:                 0
% 2.41/0.98  inst_inst_num_from_inst_to_res:         0
% 2.41/0.98  inst_dismatching_checking_time:         0.
% 2.41/0.98  
% 2.41/0.98  ------ Resolution
% 2.41/0.98  
% 2.41/0.98  res_num_of_clauses:                     0
% 2.41/0.98  res_num_in_passive:                     0
% 2.41/0.98  res_num_in_active:                      0
% 2.41/0.98  res_num_of_loops:                       112
% 2.41/0.98  res_forward_subset_subsumed:            56
% 2.41/0.98  res_backward_subset_subsumed:           0
% 2.41/0.98  res_forward_subsumed:                   0
% 2.41/0.98  res_backward_subsumed:                  0
% 2.41/0.98  res_forward_subsumption_resolution:     0
% 2.41/0.98  res_backward_subsumption_resolution:    0
% 2.41/0.98  res_clause_to_clause_subsumption:       115
% 2.41/0.98  res_orphan_elimination:                 0
% 2.41/0.98  res_tautology_del:                      52
% 2.41/0.98  res_num_eq_res_simplified:              0
% 2.41/0.98  res_num_sel_changes:                    0
% 2.41/0.98  res_moves_from_active_to_pass:          0
% 2.41/0.98  
% 2.41/0.98  ------ Superposition
% 2.41/0.98  
% 2.41/0.98  sup_time_total:                         0.
% 2.41/0.98  sup_time_generating:                    0.
% 2.41/0.98  sup_time_sim_full:                      0.
% 2.41/0.98  sup_time_sim_immed:                     0.
% 2.41/0.98  
% 2.41/0.98  sup_num_of_clauses:                     67
% 2.41/0.98  sup_num_in_active:                      52
% 2.41/0.98  sup_num_in_passive:                     15
% 2.41/0.98  sup_num_of_loops:                       64
% 2.41/0.98  sup_fw_superposition:                   32
% 2.41/0.98  sup_bw_superposition:                   24
% 2.41/0.98  sup_immediate_simplified:               20
% 2.41/0.98  sup_given_eliminated:                   0
% 2.41/0.98  comparisons_done:                       0
% 2.41/0.98  comparisons_avoided:                    0
% 2.41/0.98  
% 2.41/0.98  ------ Simplifications
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  sim_fw_subset_subsumed:                 1
% 2.41/0.98  sim_bw_subset_subsumed:                 3
% 2.41/0.98  sim_fw_subsumed:                        2
% 2.41/0.98  sim_bw_subsumed:                        0
% 2.41/0.98  sim_fw_subsumption_res:                 1
% 2.41/0.98  sim_bw_subsumption_res:                 0
% 2.41/0.98  sim_tautology_del:                      0
% 2.41/0.98  sim_eq_tautology_del:                   2
% 2.41/0.98  sim_eq_res_simp:                        0
% 2.41/0.98  sim_fw_demodulated:                     1
% 2.41/0.98  sim_bw_demodulated:                     11
% 2.41/0.98  sim_light_normalised:                   24
% 2.41/0.98  sim_joinable_taut:                      0
% 2.41/0.98  sim_joinable_simp:                      0
% 2.41/0.98  sim_ac_normalised:                      0
% 2.41/0.98  sim_smt_subsumption:                    0
% 2.41/0.98  
%------------------------------------------------------------------------------
