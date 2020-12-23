%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:12 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  225 (6883 expanded)
%              Number of clauses        :  151 (2184 expanded)
%              Number of leaves         :   23 (1960 expanded)
%              Depth                    :   24
%              Number of atoms          :  656 (47984 expanded)
%              Number of equality atoms :  276 (16573 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46,f45,f44])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_595,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1006,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_321,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_322,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_590,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_316,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_317,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_591,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_1029,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1006,c_590,c_591])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k2_relset_1(X1_53,X2_53,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1002,plain,
    ( k2_relset_1(X0_53,X1_53,X2_53) = k2_relat_1(X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1672,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1029,c_1002])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_596,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1026,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_596,c_590,c_591])).

cnf(c_1821,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1672,c_1026])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_367,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_368,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_372,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_25])).

cnf(c_373,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_589,plain,
    ( ~ v1_funct_2(sK2,X0_53,X1_53)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53 ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_1010,plain,
    ( k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1450,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_1010])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_594,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1007,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_1023,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1007,c_590,c_591])).

cnf(c_1453,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1450,c_1023,c_1029])).

cnf(c_1913,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1821,c_1453])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_600,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | m1_subset_1(k2_tops_2(X1_53,X2_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1003,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(k2_tops_2(X1_53,X2_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_2524,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_1003])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1914,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1821,c_1029])).

cnf(c_1915,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1821,c_1023])).

cnf(c_2852,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_32,c_1914,c_1915])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_13])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_328,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_13])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_10,c_328])).

cnf(c_587,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1012,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_3097,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_1012])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_607,plain,
    ( ~ v1_xboole_0(X0_53)
    | v1_xboole_0(k2_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_643,plain,
    ( v1_xboole_0(X0_53) != iProver_top
    | v1_xboole_0(k2_relat_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_645,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1000,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_1615,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1000])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_598,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tops_2(X1_53,X2_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1005,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tops_2(X1_53,X2_53,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_1731,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1005])).

cnf(c_1732,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1731,c_1453])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_303,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_304,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_49,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_306,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_27,c_26,c_49])).

cnf(c_592,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_306])).

cnf(c_1009,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1916,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1821,c_1009])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_599,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | v1_funct_2(k2_tops_2(X1_53,X2_53,X0_53),X2_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1004,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(k2_tops_2(X1_53,X2_53,X0_53),X2_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_1739,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1004])).

cnf(c_2516,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1739,c_32,c_1023,c_1029])).

cnf(c_2520,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2516,c_1821])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_995,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2859,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_995])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_606,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_997,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_3305,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2859,c_997])).

cnf(c_5169,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3097,c_32,c_645,c_1023,c_1615,c_1732,c_1916,c_2520,c_3305])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_391,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_392,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_25])).

cnf(c_588,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53) ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_1011,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_1174,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1272,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_1299,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1391,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1011,c_23,c_588,c_1272,c_1299])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_605,plain,
    ( ~ v1_relat_1(X0_53)
    | k9_relat_1(X0_53,k1_relat_1(X0_53)) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_998,plain,
    ( k9_relat_1(X0_53,k1_relat_1(X0_53)) = k2_relat_1(X0_53)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_3308,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3305,c_998])).

cnf(c_3376,plain,
    ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1391,c_3308])).

cnf(c_5173,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_5169,c_3376])).

cnf(c_1288,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_995])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1273,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_1300,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_1498,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_34,c_1273,c_1300])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_604,plain,
    ( ~ v1_relat_1(X0_53)
    | k10_relat_1(X0_53,k2_relat_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_999,plain,
    ( k10_relat_1(X0_53,k2_relat_1(X0_53)) = k1_relat_1(X0_53)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1503,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1498,c_999])).

cnf(c_5181,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5173,c_1503])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k1_relset_1(X1_53,X2_53,X0_53) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1001,plain,
    ( k1_relset_1(X0_53,X1_53,X2_53) = k1_relat_1(X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2861,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2852,c_1001])).

cnf(c_2860,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2852,c_1002])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_597,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1076,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_597,c_590,c_591])).

cnf(c_1456,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1453,c_1076])).

cnf(c_1912,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1821,c_1456])).

cnf(c_2944,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2860,c_1912])).

cnf(c_3140,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2861,c_2944])).

cnf(c_5108,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3140,c_32,c_645,c_1023,c_1615,c_1732,c_1916,c_2520,c_3097,c_3305])).

cnf(c_3096,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1012])).

cnf(c_610,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1382,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1483,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_612,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1270,plain,
    ( X0_53 != X1_53
    | X0_53 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1_53 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1404,plain,
    ( X0_53 = u1_struct_0(sK0)
    | X0_53 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1543,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = u1_struct_0(sK0)
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1402,plain,
    ( X0_53 != X1_53
    | X0_53 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1_53 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1605,plain,
    ( X0_53 = u1_struct_0(sK1)
    | X0_53 != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1769,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_1770,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_616,plain,
    ( ~ v1_xboole_0(X0_53)
    | v1_xboole_0(X1_53)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_1515,plain,
    ( v1_xboole_0(X0_53)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | X0_53 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_2507,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(k2_struct_0(sK1))
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_1252,plain,
    ( X0_53 != X1_53
    | k2_struct_0(sK0) != X1_53
    | k2_struct_0(sK0) = X0_53 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1873,plain,
    ( X0_53 != u1_struct_0(sK0)
    | k2_struct_0(sK0) = X0_53
    | k2_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_2907,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_relat_1(sK2) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1873])).

cnf(c_3512,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3096,c_27,c_26,c_25,c_24,c_23,c_49,c_591,c_590,c_1272,c_1299,c_1382,c_1483,c_1543,c_1769,c_1770,c_2507,c_2907])).

cnf(c_5110,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5108,c_3512])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5181,c_5110])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.98/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.99  
% 2.98/0.99  ------  iProver source info
% 2.98/0.99  
% 2.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.99  git: non_committed_changes: false
% 2.98/0.99  git: last_make_outside_of_git: false
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     num_symb
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       true
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  ------ Parsing...
% 2.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.99  ------ Proving...
% 2.98/0.99  ------ Problem Properties 
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  clauses                                 22
% 2.98/0.99  conjectures                             5
% 2.98/0.99  EPR                                     1
% 2.98/0.99  Horn                                    21
% 2.98/0.99  unary                                   8
% 2.98/0.99  binary                                  7
% 2.98/0.99  lits                                    50
% 2.98/0.99  lits eq                                 13
% 2.98/0.99  fd_pure                                 0
% 2.98/0.99  fd_pseudo                               0
% 2.98/0.99  fd_cond                                 0
% 2.98/0.99  fd_pseudo_cond                          1
% 2.98/0.99  AC symbols                              0
% 2.98/0.99  
% 2.98/0.99  ------ Schedule dynamic 5 is on 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  Current options:
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     none
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       false
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ Proving...
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  % SZS status Theorem for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  fof(f17,conjecture,(
% 2.98/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f18,negated_conjecture,(
% 2.98/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.98/0.99    inference(negated_conjecture,[],[f17])).
% 2.98/0.99  
% 2.98/0.99  fof(f41,plain,(
% 2.98/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f18])).
% 2.98/0.99  
% 2.98/0.99  fof(f42,plain,(
% 2.98/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.98/0.99    inference(flattening,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f46,plain,(
% 2.98/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f45,plain,(
% 2.98/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f44,plain,(
% 2.98/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f47,plain,(
% 2.98/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46,f45,f44])).
% 2.98/0.99  
% 2.98/0.99  fof(f73,plain,(
% 2.98/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f13,axiom,(
% 2.98/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f34,plain,(
% 2.98/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f13])).
% 2.98/0.99  
% 2.98/0.99  fof(f62,plain,(
% 2.98/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f34])).
% 2.98/0.99  
% 2.98/0.99  fof(f68,plain,(
% 2.98/0.99    l1_struct_0(sK0)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f70,plain,(
% 2.98/0.99    l1_struct_0(sK1)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f10,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f29,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.99    inference(ennf_transformation,[],[f10])).
% 2.98/0.99  
% 2.98/0.99  fof(f57,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f29])).
% 2.98/0.99  
% 2.98/0.99  fof(f74,plain,(
% 2.98/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f15,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f37,plain,(
% 2.98/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.98/0.99    inference(ennf_transformation,[],[f15])).
% 2.98/0.99  
% 2.98/0.99  fof(f38,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.98/0.99    inference(flattening,[],[f37])).
% 2.98/0.99  
% 2.98/0.99  fof(f64,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f38])).
% 2.98/0.99  
% 2.98/0.99  fof(f75,plain,(
% 2.98/0.99    v2_funct_1(sK2)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f71,plain,(
% 2.98/0.99    v1_funct_1(sK2)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f72,plain,(
% 2.98/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f16,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f39,plain,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.98/0.99    inference(ennf_transformation,[],[f16])).
% 2.98/0.99  
% 2.98/0.99  fof(f40,plain,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.98/0.99    inference(flattening,[],[f39])).
% 2.98/0.99  
% 2.98/0.99  fof(f67,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f40])).
% 2.98/0.99  
% 2.98/0.99  fof(f11,axiom,(
% 2.98/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f30,plain,(
% 2.98/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.98/0.99    inference(ennf_transformation,[],[f11])).
% 2.98/0.99  
% 2.98/0.99  fof(f31,plain,(
% 2.98/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.98/0.99    inference(flattening,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f59,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f31])).
% 2.98/0.99  
% 2.98/0.99  fof(f12,axiom,(
% 2.98/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f32,plain,(
% 2.98/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f12])).
% 2.98/0.99  
% 2.98/0.99  fof(f33,plain,(
% 2.98/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.98/0.99    inference(flattening,[],[f32])).
% 2.98/0.99  
% 2.98/0.99  fof(f43,plain,(
% 2.98/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.98/0.99    inference(nnf_transformation,[],[f33])).
% 2.98/0.99  
% 2.98/0.99  fof(f60,plain,(
% 2.98/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f43])).
% 2.98/0.99  
% 2.98/0.99  fof(f7,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f19,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.98/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.98/0.99  
% 2.98/0.99  fof(f26,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.99    inference(ennf_transformation,[],[f19])).
% 2.98/0.99  
% 2.98/0.99  fof(f54,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f26])).
% 2.98/0.99  
% 2.98/0.99  fof(f2,axiom,(
% 2.98/0.99    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f21,plain,(
% 2.98/0.99    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f2])).
% 2.98/0.99  
% 2.98/0.99  fof(f49,plain,(
% 2.98/0.99    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f21])).
% 2.98/0.99  
% 2.98/0.99  fof(f8,axiom,(
% 2.98/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f27,plain,(
% 2.98/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f8])).
% 2.98/0.99  
% 2.98/0.99  fof(f55,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f27])).
% 2.98/0.99  
% 2.98/0.99  fof(f65,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f40])).
% 2.98/0.99  
% 2.98/0.99  fof(f14,axiom,(
% 2.98/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f35,plain,(
% 2.98/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f14])).
% 2.98/0.99  
% 2.98/0.99  fof(f36,plain,(
% 2.98/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.98/0.99    inference(flattening,[],[f35])).
% 2.98/0.99  
% 2.98/0.99  fof(f63,plain,(
% 2.98/0.99    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f69,plain,(
% 2.98/0.99    ~v2_struct_0(sK1)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  fof(f66,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f40])).
% 2.98/0.99  
% 2.98/0.99  fof(f1,axiom,(
% 2.98/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f20,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f1])).
% 2.98/0.99  
% 2.98/0.99  fof(f48,plain,(
% 2.98/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f20])).
% 2.98/0.99  
% 2.98/0.99  fof(f3,axiom,(
% 2.98/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f50,plain,(
% 2.98/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f3])).
% 2.98/0.99  
% 2.98/0.99  fof(f6,axiom,(
% 2.98/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f24,plain,(
% 2.98/0.99    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f6])).
% 2.98/0.99  
% 2.98/0.99  fof(f25,plain,(
% 2.98/0.99    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.98/0.99    inference(flattening,[],[f24])).
% 2.98/0.99  
% 2.98/0.99  fof(f53,plain,(
% 2.98/0.99    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f25])).
% 2.98/0.99  
% 2.98/0.99  fof(f4,axiom,(
% 2.98/0.99    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f22,plain,(
% 2.98/0.99    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f4])).
% 2.98/0.99  
% 2.98/0.99  fof(f51,plain,(
% 2.98/0.99    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f22])).
% 2.98/0.99  
% 2.98/0.99  fof(f5,axiom,(
% 2.98/0.99    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f23,plain,(
% 2.98/0.99    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f5])).
% 2.98/0.99  
% 2.98/0.99  fof(f52,plain,(
% 2.98/0.99    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f23])).
% 2.98/0.99  
% 2.98/0.99  fof(f9,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f28,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.99    inference(ennf_transformation,[],[f9])).
% 2.98/0.99  
% 2.98/0.99  fof(f56,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f28])).
% 2.98/0.99  
% 2.98/0.99  fof(f76,plain,(
% 2.98/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.98/0.99    inference(cnf_transformation,[],[f47])).
% 2.98/0.99  
% 2.98/0.99  cnf(c_23,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_595,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1006,plain,
% 2.98/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_14,plain,
% 2.98/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_28,negated_conjecture,
% 2.98/0.99      ( l1_struct_0(sK0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_321,plain,
% 2.98/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_322,plain,
% 2.98/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_321]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_590,plain,
% 2.98/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_322]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_26,negated_conjecture,
% 2.98/0.99      ( l1_struct_0(sK1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_316,plain,
% 2.98/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_317,plain,
% 2.98/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_316]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_591,plain,
% 2.98/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_317]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1029,plain,
% 2.98/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.98/0.99      inference(light_normalisation,[status(thm)],[c_1006,c_590,c_591]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_9,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_601,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/0.99      | k2_relset_1(X1_53,X2_53,X0_53) = k2_relat_1(X0_53) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1002,plain,
% 2.98/0.99      ( k2_relset_1(X0_53,X1_53,X2_53) = k2_relat_1(X2_53)
% 2.98/0.99      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1672,plain,
% 2.98/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1029,c_1002]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_22,negated_conjecture,
% 2.98/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_596,negated_conjecture,
% 2.98/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1026,plain,
% 2.98/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/0.99      inference(light_normalisation,[status(thm)],[c_596,c_590,c_591]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1821,plain,
% 2.98/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_1672,c_1026]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_16,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | ~ v2_funct_1(X0)
% 2.98/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.98/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.98/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_21,negated_conjecture,
% 2.98/0.99      ( v2_funct_1(sK2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_367,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.98/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.98/0.99      | sK2 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_368,plain,
% 2.98/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.98/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.98/0.99      | ~ v1_funct_1(sK2)
% 2.98/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.98/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_25,negated_conjecture,
% 2.98/0.99      ( v1_funct_1(sK2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_372,plain,
% 2.98/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.98/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.98/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.98/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_368,c_25]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_373,plain,
% 2.98/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.98/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.98/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.98/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_372]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_589,plain,
% 2.98/0.99      ( ~ v1_funct_2(sK2,X0_53,X1_53)
% 2.98/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.98/0.99      | k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
% 2.98/0.99      | k2_relset_1(X0_53,X1_53,sK2) != X1_53 ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_373]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1010,plain,
% 2.98/0.99      ( k2_tops_2(X0_53,X1_53,sK2) = k2_funct_1(sK2)
% 2.98/0.99      | k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 2.98/0.99      | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
% 2.98/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1450,plain,
% 2.98/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.98/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1026,c_1010]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_24,negated_conjecture,
% 2.98/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_594,negated_conjecture,
% 2.98/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1007,plain,
% 2.98/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1023,plain,
% 2.98/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.98/0.99      inference(light_normalisation,[status(thm)],[c_1007,c_590,c_591]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1453,plain,
% 2.98/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_1450,c_1023,c_1029]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1913,plain,
% 2.98/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_1821,c_1453]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_17,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.98/0.99      | ~ v1_funct_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_600,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 2.98/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/0.99      | m1_subset_1(k2_tops_2(X1_53,X2_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
% 2.98/0.99      | ~ v1_funct_1(X0_53) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1003,plain,
% 2.98/0.99      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 2.98/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 2.98/0.99      | m1_subset_1(k2_tops_2(X1_53,X2_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) = iProver_top
% 2.98/0.99      | v1_funct_1(X0_53) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2524,plain,
% 2.98/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.98/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.98/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.98/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1913,c_1003]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_32,plain,
% 2.98/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1914,plain,
% 2.98/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_1821,c_1029]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1915,plain,
% 2.98/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_1821,c_1023]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2852,plain,
% 2.98/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2524,c_32,c_1914,c_1915]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_10,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | v1_partfun1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | v1_xboole_0(X2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_13,plain,
% 2.98/0.99      ( ~ v1_partfun1(X0,X1)
% 2.98/0.99      | ~ v4_relat_1(X0,X1)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | k1_relat_1(X0) = X1 ),
% 2.98/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_417,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ v4_relat_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | v1_xboole_0(X2)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | k1_relat_1(X0) = X1 ),
% 2.98/0.99      inference(resolution,[status(thm)],[c_10,c_13]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6,plain,
% 2.98/0.99      ( v4_relat_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_328,plain,
% 2.98/0.99      ( ~ v1_partfun1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | k1_relat_1(X0) = X1 ),
% 2.98/0.99      inference(resolution,[status(thm)],[c_6,c_13]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_421,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | v1_xboole_0(X2)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | k1_relat_1(X0) = X1 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_417,c_10,c_328]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_587,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 2.98/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/0.99      | ~ v1_funct_1(X0_53)
% 2.98/0.99      | v1_xboole_0(X2_53)
% 2.98/0.99      | ~ v1_relat_1(X0_53)
% 2.98/0.99      | k1_relat_1(X0_53) = X1_53 ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_421]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1012,plain,
% 2.98/0.99      ( k1_relat_1(X0_53) = X1_53
% 2.98/0.99      | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 2.98/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 2.98/0.99      | v1_funct_1(X0_53) != iProver_top
% 2.98/0.99      | v1_xboole_0(X2_53) = iProver_top
% 2.98/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3097,plain,
% 2.98/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.98/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.98/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.98/0.99      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 2.98/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2852,c_1012]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1,plain,
% 2.98/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_607,plain,
% 2.98/0.99      ( ~ v1_xboole_0(X0_53) | v1_xboole_0(k2_relat_1(X0_53)) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_643,plain,
% 2.98/0.99      ( v1_xboole_0(X0_53) != iProver_top
% 2.98/0.99      | v1_xboole_0(k2_relat_1(X0_53)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_645,plain,
% 2.98/0.99      ( v1_xboole_0(k2_relat_1(sK2)) = iProver_top
% 2.98/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_643]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_xboole_0(X1)
% 2.98/0.99      | v1_xboole_0(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_603,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/0.99      | ~ v1_xboole_0(X1_53)
% 2.98/0.99      | v1_xboole_0(X0_53) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1000,plain,
% 2.98/0.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 2.98/0.99      | v1_xboole_0(X1_53) != iProver_top
% 2.98/0.99      | v1_xboole_0(X0_53) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1615,plain,
% 2.98/0.99      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
% 2.98/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1029,c_1000]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_19,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_598,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 2.98/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/0.99      | ~ v1_funct_1(X0_53)
% 2.98/0.99      | v1_funct_1(k2_tops_2(X1_53,X2_53,X0_53)) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1005,plain,
% 2.98/0.99      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 2.98/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 2.98/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.98/1.00      | v1_funct_1(k2_tops_2(X1_53,X2_53,X0_53)) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1731,plain,
% 2.98/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
% 2.98/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1029,c_1005]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1732,plain,
% 2.98/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.98/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1731,c_1453]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_15,plain,
% 2.98/1.00      ( v2_struct_0(X0)
% 2.98/1.00      | ~ l1_struct_0(X0)
% 2.98/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_27,negated_conjecture,
% 2.98/1.00      ( ~ v2_struct_0(sK1) ),
% 2.98/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_303,plain,
% 2.98/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_304,plain,
% 2.98/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_49,plain,
% 2.98/1.00      ( v2_struct_0(sK1)
% 2.98/1.00      | ~ l1_struct_0(sK1)
% 2.98/1.00      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_306,plain,
% 2.98/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_304,c_27,c_26,c_49]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_592,plain,
% 2.98/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_306]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1009,plain,
% 2.98/1.00      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1916,plain,
% 2.98/1.00      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_1821,c_1009]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_18,plain,
% 2.98/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/1.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 2.98/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.00      | ~ v1_funct_1(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_599,plain,
% 2.98/1.00      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 2.98/1.00      | v1_funct_2(k2_tops_2(X1_53,X2_53,X0_53),X2_53,X1_53)
% 2.98/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/1.00      | ~ v1_funct_1(X0_53) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1004,plain,
% 2.98/1.00      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 2.98/1.00      | v1_funct_2(k2_tops_2(X1_53,X2_53,X0_53),X2_53,X1_53) = iProver_top
% 2.98/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 2.98/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1739,plain,
% 2.98/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.98/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1453,c_1004]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2516,plain,
% 2.98/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_1739,c_32,c_1023,c_1029]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2520,plain,
% 2.98/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_2516,c_1821]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_0,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/1.00      | ~ v1_relat_1(X1)
% 2.98/1.00      | v1_relat_1(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_608,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.98/1.00      | ~ v1_relat_1(X1_53)
% 2.98/1.00      | v1_relat_1(X0_53) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_995,plain,
% 2.98/1.00      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 2.98/1.00      | v1_relat_1(X1_53) != iProver_top
% 2.98/1.00      | v1_relat_1(X0_53) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2859,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))) != iProver_top
% 2.98/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_2852,c_995]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_606,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_997,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3305,plain,
% 2.98/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.98/1.00      inference(forward_subsumption_resolution,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_2859,c_997]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5169,plain,
% 2.98/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_3097,c_32,c_645,c_1023,c_1615,c_1732,c_1916,c_2520,
% 2.98/1.00                 c_3305]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5,plain,
% 2.98/1.00      ( ~ v1_funct_1(X0)
% 2.98/1.00      | ~ v2_funct_1(X0)
% 2.98/1.00      | ~ v1_relat_1(X0)
% 2.98/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.98/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_391,plain,
% 2.98/1.00      ( ~ v1_funct_1(X0)
% 2.98/1.00      | ~ v1_relat_1(X0)
% 2.98/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.98/1.00      | sK2 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_392,plain,
% 2.98/1.00      ( ~ v1_funct_1(sK2)
% 2.98/1.00      | ~ v1_relat_1(sK2)
% 2.98/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_396,plain,
% 2.98/1.00      ( ~ v1_relat_1(sK2)
% 2.98/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_392,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_588,plain,
% 2.98/1.00      ( ~ v1_relat_1(sK2)
% 2.98/1.00      | k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_396]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1011,plain,
% 2.98/1.00      ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53)
% 2.98/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1174,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/1.00      | v1_relat_1(X0_53)
% 2.98/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_608]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1272,plain,
% 2.98/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.98/1.00      | v1_relat_1(sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1174]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1299,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_606]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1391,plain,
% 2.98/1.00      ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_1011,c_23,c_588,c_1272,c_1299]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3,plain,
% 2.98/1.00      ( ~ v1_relat_1(X0)
% 2.98/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_605,plain,
% 2.98/1.00      ( ~ v1_relat_1(X0_53)
% 2.98/1.00      | k9_relat_1(X0_53,k1_relat_1(X0_53)) = k2_relat_1(X0_53) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_998,plain,
% 2.98/1.00      ( k9_relat_1(X0_53,k1_relat_1(X0_53)) = k2_relat_1(X0_53)
% 2.98/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3308,plain,
% 2.98/1.00      ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_3305,c_998]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3376,plain,
% 2.98/1.00      ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1391,c_3308]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5173,plain,
% 2.98/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_5169,c_3376]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1288,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.98/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1029,c_995]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_34,plain,
% 2.98/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1273,plain,
% 2.98/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.98/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.98/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1300,plain,
% 2.98/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1498,plain,
% 2.98/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_1288,c_34,c_1273,c_1300]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_4,plain,
% 2.98/1.00      ( ~ v1_relat_1(X0)
% 2.98/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_604,plain,
% 2.98/1.00      ( ~ v1_relat_1(X0_53)
% 2.98/1.00      | k10_relat_1(X0_53,k2_relat_1(X0_53)) = k1_relat_1(X0_53) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_999,plain,
% 2.98/1.00      ( k10_relat_1(X0_53,k2_relat_1(X0_53)) = k1_relat_1(X0_53)
% 2.98/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1503,plain,
% 2.98/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1498,c_999]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5181,plain,
% 2.98/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_5173,c_1503]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_8,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_602,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.98/1.00      | k1_relset_1(X1_53,X2_53,X0_53) = k1_relat_1(X0_53) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1001,plain,
% 2.98/1.00      ( k1_relset_1(X0_53,X1_53,X2_53) = k1_relat_1(X2_53)
% 2.98/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2861,plain,
% 2.98/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_2852,c_1001]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2860,plain,
% 2.98/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_2852,c_1002]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_20,negated_conjecture,
% 2.98/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.98/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.98/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_597,negated_conjecture,
% 2.98/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.98/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1076,plain,
% 2.98/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.98/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_597,c_590,c_591]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1456,plain,
% 2.98/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.98/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_1453,c_1076]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1912,plain,
% 2.98/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.98/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_1821,c_1456]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2944,plain,
% 2.98/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.98/1.00      | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_2860,c_1912]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3140,plain,
% 2.98/1.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.98/1.00      | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_2861,c_2944]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5108,plain,
% 2.98/1.00      ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_3140,c_32,c_645,c_1023,c_1615,c_1732,c_1916,c_2520,
% 2.98/1.00                 c_3097,c_3305]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3096,plain,
% 2.98/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.98/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.98/1.00      | v1_funct_1(sK2) != iProver_top
% 2.98/1.00      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
% 2.98/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1914,c_1012]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_610,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1382,plain,
% 2.98/1.00      ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_610]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1483,plain,
% 2.98/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.00      | ~ v1_funct_1(sK2)
% 2.98/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.98/1.00      | ~ v1_relat_1(sK2)
% 2.98/1.00      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_587]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_612,plain,
% 2.98/1.00      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 2.98/1.00      theory(equality) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1270,plain,
% 2.98/1.00      ( X0_53 != X1_53
% 2.98/1.00      | X0_53 = u1_struct_0(sK0)
% 2.98/1.00      | u1_struct_0(sK0) != X1_53 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_612]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1404,plain,
% 2.98/1.00      ( X0_53 = u1_struct_0(sK0)
% 2.98/1.00      | X0_53 != k2_struct_0(sK0)
% 2.98/1.00      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1270]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1543,plain,
% 2.98/1.00      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 2.98/1.00      | k2_struct_0(sK0) = u1_struct_0(sK0)
% 2.98/1.00      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1404]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1402,plain,
% 2.98/1.00      ( X0_53 != X1_53
% 2.98/1.00      | X0_53 = u1_struct_0(sK1)
% 2.98/1.00      | u1_struct_0(sK1) != X1_53 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_612]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1605,plain,
% 2.98/1.00      ( X0_53 = u1_struct_0(sK1)
% 2.98/1.00      | X0_53 != k2_struct_0(sK1)
% 2.98/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1402]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1769,plain,
% 2.98/1.00      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.98/1.00      | k2_struct_0(sK1) = u1_struct_0(sK1)
% 2.98/1.00      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1605]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1770,plain,
% 2.98/1.00      ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_610]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_616,plain,
% 2.98/1.00      ( ~ v1_xboole_0(X0_53) | v1_xboole_0(X1_53) | X1_53 != X0_53 ),
% 2.98/1.00      theory(equality) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1515,plain,
% 2.98/1.00      ( v1_xboole_0(X0_53)
% 2.98/1.00      | ~ v1_xboole_0(u1_struct_0(sK1))
% 2.98/1.00      | X0_53 != u1_struct_0(sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_616]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2507,plain,
% 2.98/1.00      ( ~ v1_xboole_0(u1_struct_0(sK1))
% 2.98/1.00      | v1_xboole_0(k2_struct_0(sK1))
% 2.98/1.00      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1515]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1252,plain,
% 2.98/1.00      ( X0_53 != X1_53
% 2.98/1.00      | k2_struct_0(sK0) != X1_53
% 2.98/1.00      | k2_struct_0(sK0) = X0_53 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_612]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1873,plain,
% 2.98/1.00      ( X0_53 != u1_struct_0(sK0)
% 2.98/1.00      | k2_struct_0(sK0) = X0_53
% 2.98/1.00      | k2_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1252]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2907,plain,
% 2.98/1.00      ( k2_struct_0(sK0) != u1_struct_0(sK0)
% 2.98/1.00      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.98/1.00      | k1_relat_1(sK2) != u1_struct_0(sK0) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1873]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3512,plain,
% 2.98/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_3096,c_27,c_26,c_25,c_24,c_23,c_49,c_591,c_590,c_1272,
% 2.98/1.00                 c_1299,c_1382,c_1483,c_1543,c_1769,c_1770,c_2507,c_2907]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5110,plain,
% 2.98/1.00      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_5108,c_3512]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(contradiction,plain,
% 2.98/1.00      ( $false ),
% 2.98/1.00      inference(minisat,[status(thm)],[c_5181,c_5110]) ).
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  ------                               Statistics
% 2.98/1.00  
% 2.98/1.00  ------ General
% 2.98/1.00  
% 2.98/1.00  abstr_ref_over_cycles:                  0
% 2.98/1.00  abstr_ref_under_cycles:                 0
% 2.98/1.00  gc_basic_clause_elim:                   0
% 2.98/1.00  forced_gc_time:                         0
% 2.98/1.00  parsing_time:                           0.011
% 2.98/1.00  unif_index_cands_time:                  0.
% 2.98/1.00  unif_index_add_time:                    0.
% 2.98/1.00  orderings_time:                         0.
% 2.98/1.00  out_proof_time:                         0.012
% 2.98/1.00  total_time:                             0.217
% 2.98/1.00  num_of_symbols:                         59
% 2.98/1.00  num_of_terms:                           4908
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing
% 2.98/1.00  
% 2.98/1.00  num_of_splits:                          0
% 2.98/1.00  num_of_split_atoms:                     0
% 2.98/1.00  num_of_reused_defs:                     0
% 2.98/1.00  num_eq_ax_congr_red:                    12
% 2.98/1.00  num_of_sem_filtered_clauses:            1
% 2.98/1.00  num_of_subtypes:                        3
% 2.98/1.00  monotx_restored_types:                  1
% 2.98/1.00  sat_num_of_epr_types:                   0
% 2.98/1.00  sat_num_of_non_cyclic_types:            0
% 2.98/1.00  sat_guarded_non_collapsed_types:        0
% 2.98/1.00  num_pure_diseq_elim:                    0
% 2.98/1.00  simp_replaced_by:                       0
% 2.98/1.00  res_preprocessed:                       127
% 2.98/1.00  prep_upred:                             0
% 2.98/1.00  prep_unflattend:                        9
% 2.98/1.00  smt_new_axioms:                         0
% 2.98/1.00  pred_elim_cands:                        5
% 2.98/1.00  pred_elim:                              5
% 2.98/1.00  pred_elim_cl:                           6
% 2.98/1.00  pred_elim_cycles:                       8
% 2.98/1.00  merged_defs:                            0
% 2.98/1.00  merged_defs_ncl:                        0
% 2.98/1.00  bin_hyper_res:                          0
% 2.98/1.00  prep_cycles:                            4
% 2.98/1.00  pred_elim_time:                         0.003
% 2.98/1.00  splitting_time:                         0.
% 2.98/1.00  sem_filter_time:                        0.
% 2.98/1.00  monotx_time:                            0.
% 2.98/1.00  subtype_inf_time:                       0.001
% 2.98/1.00  
% 2.98/1.00  ------ Problem properties
% 2.98/1.00  
% 2.98/1.00  clauses:                                22
% 2.98/1.00  conjectures:                            5
% 2.98/1.00  epr:                                    1
% 2.98/1.00  horn:                                   21
% 2.98/1.00  ground:                                 8
% 2.98/1.00  unary:                                  8
% 2.98/1.00  binary:                                 7
% 2.98/1.00  lits:                                   50
% 2.98/1.00  lits_eq:                                13
% 2.98/1.00  fd_pure:                                0
% 2.98/1.00  fd_pseudo:                              0
% 2.98/1.00  fd_cond:                                0
% 2.98/1.00  fd_pseudo_cond:                         1
% 2.98/1.00  ac_symbols:                             0
% 2.98/1.00  
% 2.98/1.00  ------ Propositional Solver
% 2.98/1.00  
% 2.98/1.00  prop_solver_calls:                      30
% 2.98/1.00  prop_fast_solver_calls:                 838
% 2.98/1.00  smt_solver_calls:                       0
% 2.98/1.00  smt_fast_solver_calls:                  0
% 2.98/1.00  prop_num_of_clauses:                    2093
% 2.98/1.00  prop_preprocess_simplified:             6919
% 2.98/1.00  prop_fo_subsumed:                       35
% 2.98/1.00  prop_solver_time:                       0.
% 2.98/1.00  smt_solver_time:                        0.
% 2.98/1.00  smt_fast_solver_time:                   0.
% 2.98/1.00  prop_fast_solver_time:                  0.
% 2.98/1.00  prop_unsat_core_time:                   0.
% 2.98/1.00  
% 2.98/1.00  ------ QBF
% 2.98/1.00  
% 2.98/1.00  qbf_q_res:                              0
% 2.98/1.00  qbf_num_tautologies:                    0
% 2.98/1.00  qbf_prep_cycles:                        0
% 2.98/1.00  
% 2.98/1.00  ------ BMC1
% 2.98/1.00  
% 2.98/1.00  bmc1_current_bound:                     -1
% 2.98/1.00  bmc1_last_solved_bound:                 -1
% 2.98/1.00  bmc1_unsat_core_size:                   -1
% 2.98/1.00  bmc1_unsat_core_parents_size:           -1
% 2.98/1.00  bmc1_merge_next_fun:                    0
% 2.98/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.00  
% 2.98/1.00  ------ Instantiation
% 2.98/1.00  
% 2.98/1.00  inst_num_of_clauses:                    712
% 2.98/1.00  inst_num_in_passive:                    384
% 2.98/1.00  inst_num_in_active:                     317
% 2.98/1.00  inst_num_in_unprocessed:                11
% 2.98/1.00  inst_num_of_loops:                      360
% 2.98/1.00  inst_num_of_learning_restarts:          0
% 2.98/1.00  inst_num_moves_active_passive:          38
% 2.98/1.00  inst_lit_activity:                      0
% 2.98/1.00  inst_lit_activity_moves:                0
% 2.98/1.00  inst_num_tautologies:                   0
% 2.98/1.00  inst_num_prop_implied:                  0
% 2.98/1.00  inst_num_existing_simplified:           0
% 2.98/1.00  inst_num_eq_res_simplified:             0
% 2.98/1.00  inst_num_child_elim:                    0
% 2.98/1.00  inst_num_of_dismatching_blockings:      208
% 2.98/1.00  inst_num_of_non_proper_insts:           590
% 2.98/1.00  inst_num_of_duplicates:                 0
% 2.98/1.00  inst_inst_num_from_inst_to_res:         0
% 2.98/1.00  inst_dismatching_checking_time:         0.
% 2.98/1.00  
% 2.98/1.00  ------ Resolution
% 2.98/1.00  
% 2.98/1.00  res_num_of_clauses:                     0
% 2.98/1.00  res_num_in_passive:                     0
% 2.98/1.00  res_num_in_active:                      0
% 2.98/1.00  res_num_of_loops:                       131
% 2.98/1.00  res_forward_subset_subsumed:            49
% 2.98/1.00  res_backward_subset_subsumed:           0
% 2.98/1.00  res_forward_subsumed:                   0
% 2.98/1.00  res_backward_subsumed:                  0
% 2.98/1.00  res_forward_subsumption_resolution:     0
% 2.98/1.00  res_backward_subsumption_resolution:    0
% 2.98/1.00  res_clause_to_clause_subsumption:       100
% 2.98/1.00  res_orphan_elimination:                 0
% 2.98/1.00  res_tautology_del:                      44
% 2.98/1.00  res_num_eq_res_simplified:              0
% 2.98/1.00  res_num_sel_changes:                    0
% 2.98/1.00  res_moves_from_active_to_pass:          0
% 2.98/1.00  
% 2.98/1.00  ------ Superposition
% 2.98/1.00  
% 2.98/1.00  sup_time_total:                         0.
% 2.98/1.00  sup_time_generating:                    0.
% 2.98/1.00  sup_time_sim_full:                      0.
% 2.98/1.00  sup_time_sim_immed:                     0.
% 2.98/1.00  
% 2.98/1.00  sup_num_of_clauses:                     52
% 2.98/1.00  sup_num_in_active:                      43
% 2.98/1.00  sup_num_in_passive:                     9
% 2.98/1.00  sup_num_of_loops:                       70
% 2.98/1.00  sup_fw_superposition:                   18
% 2.98/1.00  sup_bw_superposition:                   45
% 2.98/1.00  sup_immediate_simplified:               21
% 2.98/1.00  sup_given_eliminated:                   0
% 2.98/1.00  comparisons_done:                       0
% 2.98/1.00  comparisons_avoided:                    0
% 2.98/1.00  
% 2.98/1.00  ------ Simplifications
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  sim_fw_subset_subsumed:                 16
% 2.98/1.00  sim_bw_subset_subsumed:                 1
% 2.98/1.00  sim_fw_subsumed:                        1
% 2.98/1.00  sim_bw_subsumed:                        0
% 2.98/1.00  sim_fw_subsumption_res:                 1
% 2.98/1.00  sim_bw_subsumption_res:                 0
% 2.98/1.00  sim_tautology_del:                      0
% 2.98/1.00  sim_eq_tautology_del:                   1
% 2.98/1.00  sim_eq_res_simp:                        0
% 2.98/1.00  sim_fw_demodulated:                     0
% 2.98/1.00  sim_bw_demodulated:                     29
% 2.98/1.00  sim_light_normalised:                   13
% 2.98/1.00  sim_joinable_taut:                      0
% 2.98/1.00  sim_joinable_simp:                      0
% 2.98/1.00  sim_ac_normalised:                      0
% 2.98/1.00  sim_smt_subsumption:                    0
% 2.98/1.00  
%------------------------------------------------------------------------------
