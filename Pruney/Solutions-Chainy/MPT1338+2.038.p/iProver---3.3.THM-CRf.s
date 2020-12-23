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
% DateTime   : Thu Dec  3 12:17:07 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  185 (2240 expanded)
%              Number of clauses        :  115 ( 620 expanded)
%              Number of leaves         :   24 ( 681 expanded)
%              Depth                    :   23
%              Number of atoms          :  585 (16365 expanded)
%              Number of equality atoms :  271 (5681 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X1) )
        & v2_funct_1(sK4)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
            ( ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(sK3) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_struct_0(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(sK2)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) )
    & v2_funct_1(sK4)
    & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f44,f43,f42])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f38])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK1(X0),X0)
        & k1_xboole_0 != sK1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK1(X0),X0)
          & k1_xboole_0 != sK1(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f40])).

fof(f67,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1219,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_403,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_404,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_408,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_409,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1258,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1219,c_404,c_409])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1229,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1911,plain,
    ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1258,c_1229])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1255,plain,
    ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_30,c_404,c_409])).

cnf(c_2040,plain,
    ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_1911,c_1255])).

cnf(c_2437,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2040,c_1258])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1223,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3382,plain,
    ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_struct_0(sK2)
    | k2_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_1223])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1230,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2188,plain,
    ( k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1258,c_1230])).

cnf(c_2724,plain,
    ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2188,c_2040])).

cnf(c_3386,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4)
    | k2_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3382,c_2724])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1218,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1252,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1218,c_404,c_409])).

cnf(c_2438,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2040,c_1252])).

cnf(c_3672,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | k2_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3386,c_2438])).

cnf(c_3673,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3672])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_458,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_462,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK4,X0,X1)
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_33])).

cnf(c_463,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_1214,plain,
    ( k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1785,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_1214])).

cnf(c_1788,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1785,c_1258,c_1252])).

cnf(c_2436,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_funct_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2040,c_1788])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1222,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4041,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2436,c_1222])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4372,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4041,c_40,c_2437,c_2438])).

cnf(c_4381,plain,
    ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4372,c_1229])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_495,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_496,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_498,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_33])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_498])).

cnf(c_521,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_1213,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_1446,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_1904,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1213,c_31,c_1446])).

cnf(c_4390,plain,
    ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_4381,c_1904])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1349,plain,
    ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_28,c_404,c_409])).

cnf(c_1791,plain,
    ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_1788,c_1349])).

cnf(c_2435,plain,
    ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2040,c_1791])).

cnf(c_4451,plain,
    ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k2_struct_0(sK2) != k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4390,c_2435])).

cnf(c_4380,plain,
    ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4372,c_1230])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_481,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_482,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_484,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_33])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_484])).

cnf(c_533,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_1212,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_1862,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1212,c_31,c_1449])).

cnf(c_4393,plain,
    ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_4380,c_1862])).

cnf(c_4567,plain,
    ( k2_struct_0(sK2) != k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4451,c_4393])).

cnf(c_4570,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3673,c_4567])).

cnf(c_20,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_377,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_378,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_380,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_34])).

cnf(c_1216,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1249,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1216,c_404])).

cnf(c_2439,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2040,c_1249])).

cnf(c_4585,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4570,c_2439])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_23])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_tarski(k1_zfmisc_1(X1)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_2596,plain,
    ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0))
    | k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
    | k1_xboole_0 = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_2603,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
    | k1_xboole_0 = sK0(sK3)
    | m1_subset_1(sK0(sK3),k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2596])).

cnf(c_2605,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK0(sK3)
    | m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_765,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1628,plain,
    ( X0 != X1
    | sK0(sK3) != X1
    | sK0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1888,plain,
    ( X0 != sK0(sK3)
    | sK0(sK3) = X0
    | sK0(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_1890,plain,
    ( sK0(sK3) != sK0(sK3)
    | sK0(sK3) = k1_xboole_0
    | k1_xboole_0 != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_764,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1886,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_780,plain,
    ( X0 != X1
    | sK0(X0) = sK0(X1) ),
    theory(equality)).

cnf(c_1630,plain,
    ( sK0(sK3) = sK0(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1885,plain,
    ( sK0(sK3) = sK0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_766,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1480,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0(sK3))
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1482,plain,
    ( v1_xboole_0(sK0(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_388,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_389,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_118,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_105,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4585,c_2605,c_1890,c_1886,c_1885,c_1482,c_389,c_0,c_118,c_107,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.37/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.06  
% 0.37/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.06  
% 0.37/1.06  ------  iProver source info
% 0.37/1.06  
% 0.37/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.06  git: non_committed_changes: false
% 0.37/1.06  git: last_make_outside_of_git: false
% 0.37/1.06  
% 0.37/1.06  ------ 
% 0.37/1.06  
% 0.37/1.06  ------ Input Options
% 0.37/1.06  
% 0.37/1.06  --out_options                           all
% 0.37/1.06  --tptp_safe_out                         true
% 0.37/1.06  --problem_path                          ""
% 0.37/1.06  --include_path                          ""
% 0.37/1.06  --clausifier                            res/vclausify_rel
% 0.37/1.06  --clausifier_options                    --mode clausify
% 0.37/1.06  --stdin                                 false
% 0.37/1.06  --stats_out                             all
% 0.37/1.06  
% 0.37/1.06  ------ General Options
% 0.37/1.06  
% 0.37/1.06  --fof                                   false
% 0.37/1.06  --time_out_real                         305.
% 0.37/1.06  --time_out_virtual                      -1.
% 0.37/1.06  --symbol_type_check                     false
% 0.37/1.06  --clausify_out                          false
% 0.37/1.06  --sig_cnt_out                           false
% 0.37/1.06  --trig_cnt_out                          false
% 0.37/1.06  --trig_cnt_out_tolerance                1.
% 0.37/1.06  --trig_cnt_out_sk_spl                   false
% 0.37/1.06  --abstr_cl_out                          false
% 0.37/1.06  
% 0.37/1.06  ------ Global Options
% 0.37/1.06  
% 0.37/1.06  --schedule                              default
% 0.37/1.06  --add_important_lit                     false
% 0.37/1.06  --prop_solver_per_cl                    1000
% 0.37/1.06  --min_unsat_core                        false
% 0.37/1.06  --soft_assumptions                      false
% 0.37/1.06  --soft_lemma_size                       3
% 0.37/1.06  --prop_impl_unit_size                   0
% 0.37/1.06  --prop_impl_unit                        []
% 0.37/1.06  --share_sel_clauses                     true
% 0.37/1.06  --reset_solvers                         false
% 0.37/1.06  --bc_imp_inh                            [conj_cone]
% 0.37/1.06  --conj_cone_tolerance                   3.
% 0.37/1.06  --extra_neg_conj                        none
% 0.37/1.06  --large_theory_mode                     true
% 0.37/1.06  --prolific_symb_bound                   200
% 0.37/1.06  --lt_threshold                          2000
% 0.37/1.06  --clause_weak_htbl                      true
% 0.37/1.06  --gc_record_bc_elim                     false
% 0.37/1.06  
% 0.37/1.06  ------ Preprocessing Options
% 0.37/1.06  
% 0.37/1.06  --preprocessing_flag                    true
% 0.37/1.06  --time_out_prep_mult                    0.1
% 0.37/1.06  --splitting_mode                        input
% 0.37/1.06  --splitting_grd                         true
% 0.37/1.06  --splitting_cvd                         false
% 0.37/1.06  --splitting_cvd_svl                     false
% 0.37/1.06  --splitting_nvd                         32
% 0.37/1.06  --sub_typing                            true
% 0.37/1.06  --prep_gs_sim                           true
% 0.37/1.06  --prep_unflatten                        true
% 0.37/1.06  --prep_res_sim                          true
% 0.37/1.06  --prep_upred                            true
% 0.37/1.06  --prep_sem_filter                       exhaustive
% 0.37/1.06  --prep_sem_filter_out                   false
% 0.37/1.06  --pred_elim                             true
% 0.37/1.06  --res_sim_input                         true
% 0.37/1.06  --eq_ax_congr_red                       true
% 0.37/1.06  --pure_diseq_elim                       true
% 0.37/1.06  --brand_transform                       false
% 0.37/1.06  --non_eq_to_eq                          false
% 0.37/1.06  --prep_def_merge                        true
% 0.37/1.06  --prep_def_merge_prop_impl              false
% 0.37/1.06  --prep_def_merge_mbd                    true
% 0.37/1.06  --prep_def_merge_tr_red                 false
% 0.37/1.06  --prep_def_merge_tr_cl                  false
% 0.37/1.06  --smt_preprocessing                     true
% 0.37/1.06  --smt_ac_axioms                         fast
% 0.37/1.06  --preprocessed_out                      false
% 0.37/1.06  --preprocessed_stats                    false
% 0.37/1.06  
% 0.37/1.06  ------ Abstraction refinement Options
% 0.37/1.06  
% 0.37/1.06  --abstr_ref                             []
% 0.37/1.06  --abstr_ref_prep                        false
% 0.37/1.06  --abstr_ref_until_sat                   false
% 0.37/1.06  --abstr_ref_sig_restrict                funpre
% 0.37/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.06  --abstr_ref_under                       []
% 0.37/1.06  
% 0.37/1.06  ------ SAT Options
% 0.37/1.06  
% 0.37/1.06  --sat_mode                              false
% 0.37/1.06  --sat_fm_restart_options                ""
% 0.37/1.06  --sat_gr_def                            false
% 0.37/1.06  --sat_epr_types                         true
% 0.37/1.06  --sat_non_cyclic_types                  false
% 0.37/1.06  --sat_finite_models                     false
% 0.37/1.06  --sat_fm_lemmas                         false
% 0.37/1.06  --sat_fm_prep                           false
% 0.37/1.06  --sat_fm_uc_incr                        true
% 0.37/1.06  --sat_out_model                         small
% 0.37/1.06  --sat_out_clauses                       false
% 0.37/1.06  
% 0.37/1.06  ------ QBF Options
% 0.37/1.06  
% 0.37/1.06  --qbf_mode                              false
% 0.37/1.06  --qbf_elim_univ                         false
% 0.37/1.06  --qbf_dom_inst                          none
% 0.37/1.06  --qbf_dom_pre_inst                      false
% 0.37/1.06  --qbf_sk_in                             false
% 0.37/1.06  --qbf_pred_elim                         true
% 0.37/1.06  --qbf_split                             512
% 0.37/1.06  
% 0.37/1.06  ------ BMC1 Options
% 0.37/1.06  
% 0.37/1.06  --bmc1_incremental                      false
% 0.37/1.06  --bmc1_axioms                           reachable_all
% 0.37/1.06  --bmc1_min_bound                        0
% 0.37/1.06  --bmc1_max_bound                        -1
% 0.37/1.06  --bmc1_max_bound_default                -1
% 0.37/1.06  --bmc1_symbol_reachability              true
% 0.37/1.06  --bmc1_property_lemmas                  false
% 0.37/1.06  --bmc1_k_induction                      false
% 0.37/1.06  --bmc1_non_equiv_states                 false
% 0.37/1.06  --bmc1_deadlock                         false
% 0.37/1.06  --bmc1_ucm                              false
% 0.37/1.06  --bmc1_add_unsat_core                   none
% 0.37/1.06  --bmc1_unsat_core_children              false
% 0.37/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.06  --bmc1_out_stat                         full
% 0.37/1.06  --bmc1_ground_init                      false
% 0.37/1.06  --bmc1_pre_inst_next_state              false
% 0.37/1.06  --bmc1_pre_inst_state                   false
% 0.37/1.06  --bmc1_pre_inst_reach_state             false
% 0.37/1.06  --bmc1_out_unsat_core                   false
% 0.37/1.06  --bmc1_aig_witness_out                  false
% 0.37/1.06  --bmc1_verbose                          false
% 0.37/1.06  --bmc1_dump_clauses_tptp                false
% 0.37/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.06  --bmc1_dump_file                        -
% 0.37/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.06  --bmc1_ucm_extend_mode                  1
% 0.37/1.06  --bmc1_ucm_init_mode                    2
% 0.37/1.06  --bmc1_ucm_cone_mode                    none
% 0.37/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.06  --bmc1_ucm_relax_model                  4
% 0.37/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.06  --bmc1_ucm_layered_model                none
% 0.37/1.06  --bmc1_ucm_max_lemma_size               10
% 0.37/1.06  
% 0.37/1.06  ------ AIG Options
% 0.37/1.06  
% 0.37/1.06  --aig_mode                              false
% 0.37/1.06  
% 0.37/1.06  ------ Instantiation Options
% 0.37/1.06  
% 0.37/1.06  --instantiation_flag                    true
% 0.37/1.06  --inst_sos_flag                         false
% 0.37/1.06  --inst_sos_phase                        true
% 0.37/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.06  --inst_lit_sel_side                     num_symb
% 0.37/1.06  --inst_solver_per_active                1400
% 0.37/1.06  --inst_solver_calls_frac                1.
% 0.37/1.06  --inst_passive_queue_type               priority_queues
% 0.37/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.06  --inst_passive_queues_freq              [25;2]
% 0.37/1.06  --inst_dismatching                      true
% 0.37/1.06  --inst_eager_unprocessed_to_passive     true
% 0.37/1.06  --inst_prop_sim_given                   true
% 0.37/1.06  --inst_prop_sim_new                     false
% 0.37/1.06  --inst_subs_new                         false
% 0.37/1.06  --inst_eq_res_simp                      false
% 0.37/1.06  --inst_subs_given                       false
% 0.37/1.06  --inst_orphan_elimination               true
% 0.37/1.06  --inst_learning_loop_flag               true
% 0.37/1.06  --inst_learning_start                   3000
% 0.37/1.06  --inst_learning_factor                  2
% 0.37/1.06  --inst_start_prop_sim_after_learn       3
% 0.37/1.06  --inst_sel_renew                        solver
% 0.37/1.06  --inst_lit_activity_flag                true
% 0.37/1.06  --inst_restr_to_given                   false
% 0.37/1.06  --inst_activity_threshold               500
% 0.37/1.06  --inst_out_proof                        true
% 0.37/1.06  
% 0.37/1.06  ------ Resolution Options
% 0.37/1.06  
% 0.37/1.06  --resolution_flag                       true
% 0.37/1.06  --res_lit_sel                           adaptive
% 0.37/1.06  --res_lit_sel_side                      none
% 0.37/1.06  --res_ordering                          kbo
% 0.37/1.06  --res_to_prop_solver                    active
% 0.37/1.06  --res_prop_simpl_new                    false
% 0.37/1.06  --res_prop_simpl_given                  true
% 0.37/1.06  --res_passive_queue_type                priority_queues
% 0.37/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.06  --res_passive_queues_freq               [15;5]
% 0.37/1.06  --res_forward_subs                      full
% 0.37/1.06  --res_backward_subs                     full
% 0.37/1.06  --res_forward_subs_resolution           true
% 0.37/1.06  --res_backward_subs_resolution          true
% 0.37/1.06  --res_orphan_elimination                true
% 0.37/1.06  --res_time_limit                        2.
% 0.37/1.06  --res_out_proof                         true
% 0.37/1.06  
% 0.37/1.06  ------ Superposition Options
% 0.37/1.06  
% 0.37/1.06  --superposition_flag                    true
% 0.37/1.06  --sup_passive_queue_type                priority_queues
% 0.37/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.06  --demod_completeness_check              fast
% 0.37/1.06  --demod_use_ground                      true
% 0.37/1.06  --sup_to_prop_solver                    passive
% 0.37/1.06  --sup_prop_simpl_new                    true
% 0.37/1.06  --sup_prop_simpl_given                  true
% 0.37/1.06  --sup_fun_splitting                     false
% 0.37/1.06  --sup_smt_interval                      50000
% 0.37/1.06  
% 0.37/1.06  ------ Superposition Simplification Setup
% 0.37/1.06  
% 0.37/1.06  --sup_indices_passive                   []
% 0.37/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.06  --sup_full_bw                           [BwDemod]
% 0.37/1.06  --sup_immed_triv                        [TrivRules]
% 0.37/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.06  --sup_immed_bw_main                     []
% 0.37/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.06  
% 0.37/1.06  ------ Combination Options
% 0.37/1.06  
% 0.37/1.06  --comb_res_mult                         3
% 0.37/1.06  --comb_sup_mult                         2
% 0.37/1.06  --comb_inst_mult                        10
% 0.37/1.06  
% 0.37/1.06  ------ Debug Options
% 0.37/1.06  
% 0.37/1.06  --dbg_backtrace                         false
% 0.37/1.06  --dbg_dump_prop_clauses                 false
% 0.37/1.06  --dbg_dump_prop_clauses_file            -
% 0.37/1.06  --dbg_out_stat                          false
% 0.37/1.06  ------ Parsing...
% 0.37/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.06  
% 0.37/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.37/1.06  
% 0.37/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.06  
% 0.37/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.37/1.06  ------ Proving...
% 0.37/1.06  ------ Problem Properties 
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  clauses                                 31
% 0.37/1.06  conjectures                             5
% 0.37/1.06  EPR                                     4
% 0.37/1.06  Horn                                    25
% 0.37/1.06  unary                                   11
% 0.37/1.06  binary                                  6
% 0.37/1.06  lits                                    73
% 0.37/1.06  lits eq                                 26
% 0.37/1.06  fd_pure                                 0
% 0.37/1.06  fd_pseudo                               0
% 0.37/1.06  fd_cond                                 4
% 0.37/1.06  fd_pseudo_cond                          0
% 0.37/1.06  AC symbols                              0
% 0.37/1.06  
% 0.37/1.06  ------ Schedule dynamic 5 is on 
% 0.37/1.06  
% 0.37/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  ------ 
% 0.37/1.06  Current options:
% 0.37/1.06  ------ 
% 0.37/1.06  
% 0.37/1.06  ------ Input Options
% 0.37/1.06  
% 0.37/1.06  --out_options                           all
% 0.37/1.06  --tptp_safe_out                         true
% 0.37/1.06  --problem_path                          ""
% 0.37/1.06  --include_path                          ""
% 0.37/1.06  --clausifier                            res/vclausify_rel
% 0.37/1.06  --clausifier_options                    --mode clausify
% 0.37/1.06  --stdin                                 false
% 0.37/1.06  --stats_out                             all
% 0.37/1.06  
% 0.37/1.06  ------ General Options
% 0.37/1.06  
% 0.37/1.06  --fof                                   false
% 0.37/1.06  --time_out_real                         305.
% 0.37/1.06  --time_out_virtual                      -1.
% 0.37/1.06  --symbol_type_check                     false
% 0.37/1.06  --clausify_out                          false
% 0.37/1.06  --sig_cnt_out                           false
% 0.37/1.06  --trig_cnt_out                          false
% 0.37/1.06  --trig_cnt_out_tolerance                1.
% 0.37/1.06  --trig_cnt_out_sk_spl                   false
% 0.37/1.06  --abstr_cl_out                          false
% 0.37/1.06  
% 0.37/1.06  ------ Global Options
% 0.37/1.06  
% 0.37/1.06  --schedule                              default
% 0.37/1.06  --add_important_lit                     false
% 0.37/1.06  --prop_solver_per_cl                    1000
% 0.37/1.06  --min_unsat_core                        false
% 0.37/1.06  --soft_assumptions                      false
% 0.37/1.06  --soft_lemma_size                       3
% 0.37/1.06  --prop_impl_unit_size                   0
% 0.37/1.06  --prop_impl_unit                        []
% 0.37/1.06  --share_sel_clauses                     true
% 0.37/1.06  --reset_solvers                         false
% 0.37/1.06  --bc_imp_inh                            [conj_cone]
% 0.37/1.06  --conj_cone_tolerance                   3.
% 0.37/1.06  --extra_neg_conj                        none
% 0.37/1.06  --large_theory_mode                     true
% 0.37/1.06  --prolific_symb_bound                   200
% 0.37/1.06  --lt_threshold                          2000
% 0.37/1.06  --clause_weak_htbl                      true
% 0.37/1.06  --gc_record_bc_elim                     false
% 0.37/1.06  
% 0.37/1.06  ------ Preprocessing Options
% 0.37/1.06  
% 0.37/1.06  --preprocessing_flag                    true
% 0.37/1.06  --time_out_prep_mult                    0.1
% 0.37/1.06  --splitting_mode                        input
% 0.37/1.06  --splitting_grd                         true
% 0.37/1.06  --splitting_cvd                         false
% 0.37/1.06  --splitting_cvd_svl                     false
% 0.37/1.06  --splitting_nvd                         32
% 0.37/1.06  --sub_typing                            true
% 0.37/1.06  --prep_gs_sim                           true
% 0.37/1.06  --prep_unflatten                        true
% 0.37/1.06  --prep_res_sim                          true
% 0.37/1.06  --prep_upred                            true
% 0.37/1.06  --prep_sem_filter                       exhaustive
% 0.37/1.06  --prep_sem_filter_out                   false
% 0.37/1.06  --pred_elim                             true
% 0.37/1.06  --res_sim_input                         true
% 0.37/1.06  --eq_ax_congr_red                       true
% 0.37/1.06  --pure_diseq_elim                       true
% 0.37/1.06  --brand_transform                       false
% 0.37/1.06  --non_eq_to_eq                          false
% 0.37/1.06  --prep_def_merge                        true
% 0.37/1.06  --prep_def_merge_prop_impl              false
% 0.37/1.06  --prep_def_merge_mbd                    true
% 0.37/1.06  --prep_def_merge_tr_red                 false
% 0.37/1.06  --prep_def_merge_tr_cl                  false
% 0.37/1.06  --smt_preprocessing                     true
% 0.37/1.06  --smt_ac_axioms                         fast
% 0.37/1.06  --preprocessed_out                      false
% 0.37/1.06  --preprocessed_stats                    false
% 0.37/1.06  
% 0.37/1.06  ------ Abstraction refinement Options
% 0.37/1.06  
% 0.37/1.06  --abstr_ref                             []
% 0.37/1.06  --abstr_ref_prep                        false
% 0.37/1.06  --abstr_ref_until_sat                   false
% 0.37/1.06  --abstr_ref_sig_restrict                funpre
% 0.37/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.06  --abstr_ref_under                       []
% 0.37/1.06  
% 0.37/1.06  ------ SAT Options
% 0.37/1.06  
% 0.37/1.06  --sat_mode                              false
% 0.37/1.06  --sat_fm_restart_options                ""
% 0.37/1.06  --sat_gr_def                            false
% 0.37/1.06  --sat_epr_types                         true
% 0.37/1.06  --sat_non_cyclic_types                  false
% 0.37/1.06  --sat_finite_models                     false
% 0.37/1.06  --sat_fm_lemmas                         false
% 0.37/1.06  --sat_fm_prep                           false
% 0.37/1.06  --sat_fm_uc_incr                        true
% 0.37/1.06  --sat_out_model                         small
% 0.37/1.06  --sat_out_clauses                       false
% 0.37/1.06  
% 0.37/1.06  ------ QBF Options
% 0.37/1.06  
% 0.37/1.06  --qbf_mode                              false
% 0.37/1.06  --qbf_elim_univ                         false
% 0.37/1.06  --qbf_dom_inst                          none
% 0.37/1.06  --qbf_dom_pre_inst                      false
% 0.37/1.06  --qbf_sk_in                             false
% 0.37/1.06  --qbf_pred_elim                         true
% 0.37/1.06  --qbf_split                             512
% 0.37/1.06  
% 0.37/1.06  ------ BMC1 Options
% 0.37/1.06  
% 0.37/1.06  --bmc1_incremental                      false
% 0.37/1.06  --bmc1_axioms                           reachable_all
% 0.37/1.06  --bmc1_min_bound                        0
% 0.37/1.06  --bmc1_max_bound                        -1
% 0.37/1.06  --bmc1_max_bound_default                -1
% 0.37/1.06  --bmc1_symbol_reachability              true
% 0.37/1.06  --bmc1_property_lemmas                  false
% 0.37/1.06  --bmc1_k_induction                      false
% 0.37/1.06  --bmc1_non_equiv_states                 false
% 0.37/1.06  --bmc1_deadlock                         false
% 0.37/1.06  --bmc1_ucm                              false
% 0.37/1.06  --bmc1_add_unsat_core                   none
% 0.37/1.06  --bmc1_unsat_core_children              false
% 0.37/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.06  --bmc1_out_stat                         full
% 0.37/1.06  --bmc1_ground_init                      false
% 0.37/1.06  --bmc1_pre_inst_next_state              false
% 0.37/1.06  --bmc1_pre_inst_state                   false
% 0.37/1.06  --bmc1_pre_inst_reach_state             false
% 0.37/1.06  --bmc1_out_unsat_core                   false
% 0.37/1.06  --bmc1_aig_witness_out                  false
% 0.37/1.06  --bmc1_verbose                          false
% 0.37/1.06  --bmc1_dump_clauses_tptp                false
% 0.37/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.06  --bmc1_dump_file                        -
% 0.37/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.06  --bmc1_ucm_extend_mode                  1
% 0.37/1.06  --bmc1_ucm_init_mode                    2
% 0.37/1.06  --bmc1_ucm_cone_mode                    none
% 0.37/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.06  --bmc1_ucm_relax_model                  4
% 0.37/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.06  --bmc1_ucm_layered_model                none
% 0.37/1.06  --bmc1_ucm_max_lemma_size               10
% 0.37/1.06  
% 0.37/1.06  ------ AIG Options
% 0.37/1.06  
% 0.37/1.06  --aig_mode                              false
% 0.37/1.06  
% 0.37/1.06  ------ Instantiation Options
% 0.37/1.06  
% 0.37/1.06  --instantiation_flag                    true
% 0.37/1.06  --inst_sos_flag                         false
% 0.37/1.06  --inst_sos_phase                        true
% 0.37/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.06  --inst_lit_sel_side                     none
% 0.37/1.06  --inst_solver_per_active                1400
% 0.37/1.06  --inst_solver_calls_frac                1.
% 0.37/1.06  --inst_passive_queue_type               priority_queues
% 0.37/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.06  --inst_passive_queues_freq              [25;2]
% 0.37/1.06  --inst_dismatching                      true
% 0.37/1.06  --inst_eager_unprocessed_to_passive     true
% 0.37/1.06  --inst_prop_sim_given                   true
% 0.37/1.06  --inst_prop_sim_new                     false
% 0.37/1.06  --inst_subs_new                         false
% 0.37/1.06  --inst_eq_res_simp                      false
% 0.37/1.06  --inst_subs_given                       false
% 0.37/1.06  --inst_orphan_elimination               true
% 0.37/1.06  --inst_learning_loop_flag               true
% 0.37/1.06  --inst_learning_start                   3000
% 0.37/1.06  --inst_learning_factor                  2
% 0.37/1.06  --inst_start_prop_sim_after_learn       3
% 0.37/1.06  --inst_sel_renew                        solver
% 0.37/1.06  --inst_lit_activity_flag                true
% 0.37/1.06  --inst_restr_to_given                   false
% 0.37/1.06  --inst_activity_threshold               500
% 0.37/1.06  --inst_out_proof                        true
% 0.37/1.06  
% 0.37/1.06  ------ Resolution Options
% 0.37/1.06  
% 0.37/1.06  --resolution_flag                       false
% 0.37/1.06  --res_lit_sel                           adaptive
% 0.37/1.06  --res_lit_sel_side                      none
% 0.37/1.06  --res_ordering                          kbo
% 0.37/1.06  --res_to_prop_solver                    active
% 0.37/1.06  --res_prop_simpl_new                    false
% 0.37/1.06  --res_prop_simpl_given                  true
% 0.37/1.06  --res_passive_queue_type                priority_queues
% 0.37/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.06  --res_passive_queues_freq               [15;5]
% 0.37/1.06  --res_forward_subs                      full
% 0.37/1.06  --res_backward_subs                     full
% 0.37/1.06  --res_forward_subs_resolution           true
% 0.37/1.06  --res_backward_subs_resolution          true
% 0.37/1.06  --res_orphan_elimination                true
% 0.37/1.06  --res_time_limit                        2.
% 0.37/1.06  --res_out_proof                         true
% 0.37/1.06  
% 0.37/1.06  ------ Superposition Options
% 0.37/1.06  
% 0.37/1.06  --superposition_flag                    true
% 0.37/1.06  --sup_passive_queue_type                priority_queues
% 0.37/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.06  --demod_completeness_check              fast
% 0.37/1.06  --demod_use_ground                      true
% 0.37/1.06  --sup_to_prop_solver                    passive
% 0.37/1.06  --sup_prop_simpl_new                    true
% 0.37/1.06  --sup_prop_simpl_given                  true
% 0.37/1.06  --sup_fun_splitting                     false
% 0.37/1.06  --sup_smt_interval                      50000
% 0.37/1.06  
% 0.37/1.06  ------ Superposition Simplification Setup
% 0.37/1.06  
% 0.37/1.06  --sup_indices_passive                   []
% 0.37/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.06  --sup_full_bw                           [BwDemod]
% 0.37/1.06  --sup_immed_triv                        [TrivRules]
% 0.37/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.06  --sup_immed_bw_main                     []
% 0.37/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.06  
% 0.37/1.06  ------ Combination Options
% 0.37/1.06  
% 0.37/1.06  --comb_res_mult                         3
% 0.37/1.06  --comb_sup_mult                         2
% 0.37/1.06  --comb_inst_mult                        10
% 0.37/1.06  
% 0.37/1.06  ------ Debug Options
% 0.37/1.06  
% 0.37/1.06  --dbg_backtrace                         false
% 0.37/1.06  --dbg_dump_prop_clauses                 false
% 0.37/1.06  --dbg_dump_prop_clauses_file            -
% 0.37/1.06  --dbg_out_stat                          false
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  ------ Proving...
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  % SZS status Theorem for theBenchmark.p
% 0.37/1.06  
% 0.37/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.06  
% 0.37/1.06  fof(f15,conjecture,(
% 0.37/1.06    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f16,negated_conjecture,(
% 0.37/1.06    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 0.37/1.06    inference(negated_conjecture,[],[f15])).
% 0.37/1.06  
% 0.37/1.06  fof(f34,plain,(
% 0.37/1.06    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.37/1.06    inference(ennf_transformation,[],[f16])).
% 0.37/1.06  
% 0.37/1.06  fof(f35,plain,(
% 0.37/1.06    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.37/1.06    inference(flattening,[],[f34])).
% 0.37/1.06  
% 0.37/1.06  fof(f44,plain,(
% 0.37/1.06    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X1)) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 0.37/1.06    introduced(choice_axiom,[])).
% 0.37/1.06  
% 0.37/1.06  fof(f43,plain,(
% 0.37/1.06    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(sK3)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))) )),
% 0.37/1.06    introduced(choice_axiom,[])).
% 0.37/1.06  
% 0.37/1.06  fof(f42,plain,(
% 0.37/1.06    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 0.37/1.06    introduced(choice_axiom,[])).
% 0.37/1.06  
% 0.37/1.06  fof(f45,plain,(
% 0.37/1.06    (((k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 0.37/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f44,f43,f42])).
% 0.37/1.06  
% 0.37/1.06  fof(f79,plain,(
% 0.37/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f10,axiom,(
% 0.37/1.06    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f26,plain,(
% 0.37/1.06    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.37/1.06    inference(ennf_transformation,[],[f10])).
% 0.37/1.06  
% 0.37/1.06  fof(f64,plain,(
% 0.37/1.06    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f26])).
% 0.37/1.06  
% 0.37/1.06  fof(f76,plain,(
% 0.37/1.06    l1_struct_0(sK3)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f74,plain,(
% 0.37/1.06    l1_struct_0(sK2)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f8,axiom,(
% 0.37/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f23,plain,(
% 0.37/1.06    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.06    inference(ennf_transformation,[],[f8])).
% 0.37/1.06  
% 0.37/1.06  fof(f57,plain,(
% 0.37/1.06    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.06    inference(cnf_transformation,[],[f23])).
% 0.37/1.06  
% 0.37/1.06  fof(f80,plain,(
% 0.37/1.06    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f9,axiom,(
% 0.37/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f24,plain,(
% 0.37/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.06    inference(ennf_transformation,[],[f9])).
% 0.37/1.06  
% 0.37/1.06  fof(f25,plain,(
% 0.37/1.06    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.06    inference(flattening,[],[f24])).
% 0.37/1.06  
% 0.37/1.06  fof(f37,plain,(
% 0.37/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.06    inference(nnf_transformation,[],[f25])).
% 0.37/1.06  
% 0.37/1.06  fof(f58,plain,(
% 0.37/1.06    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.06    inference(cnf_transformation,[],[f37])).
% 0.37/1.06  
% 0.37/1.06  fof(f7,axiom,(
% 0.37/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f22,plain,(
% 0.37/1.06    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.06    inference(ennf_transformation,[],[f7])).
% 0.37/1.06  
% 0.37/1.06  fof(f56,plain,(
% 0.37/1.06    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.06    inference(cnf_transformation,[],[f22])).
% 0.37/1.06  
% 0.37/1.06  fof(f78,plain,(
% 0.37/1.06    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f13,axiom,(
% 0.37/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f30,plain,(
% 0.37/1.06    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.37/1.06    inference(ennf_transformation,[],[f13])).
% 0.37/1.06  
% 0.37/1.06  fof(f31,plain,(
% 0.37/1.06    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.37/1.06    inference(flattening,[],[f30])).
% 0.37/1.06  
% 0.37/1.06  fof(f70,plain,(
% 0.37/1.06    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f31])).
% 0.37/1.06  
% 0.37/1.06  fof(f81,plain,(
% 0.37/1.06    v2_funct_1(sK4)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f77,plain,(
% 0.37/1.06    v1_funct_1(sK4)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f14,axiom,(
% 0.37/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f32,plain,(
% 0.37/1.06    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.37/1.06    inference(ennf_transformation,[],[f14])).
% 0.37/1.06  
% 0.37/1.06  fof(f33,plain,(
% 0.37/1.06    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.37/1.06    inference(flattening,[],[f32])).
% 0.37/1.06  
% 0.37/1.06  fof(f73,plain,(
% 0.37/1.06    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f33])).
% 0.37/1.06  
% 0.37/1.06  fof(f6,axiom,(
% 0.37/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f21,plain,(
% 0.37/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.06    inference(ennf_transformation,[],[f6])).
% 0.37/1.06  
% 0.37/1.06  fof(f55,plain,(
% 0.37/1.06    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.06    inference(cnf_transformation,[],[f21])).
% 0.37/1.06  
% 0.37/1.06  fof(f5,axiom,(
% 0.37/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f19,plain,(
% 0.37/1.06    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/1.06    inference(ennf_transformation,[],[f5])).
% 0.37/1.06  
% 0.37/1.06  fof(f20,plain,(
% 0.37/1.06    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.06    inference(flattening,[],[f19])).
% 0.37/1.06  
% 0.37/1.06  fof(f54,plain,(
% 0.37/1.06    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f20])).
% 0.37/1.06  
% 0.37/1.06  fof(f82,plain,(
% 0.37/1.06    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f53,plain,(
% 0.37/1.06    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f20])).
% 0.37/1.06  
% 0.37/1.06  fof(f11,axiom,(
% 0.37/1.06    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f27,plain,(
% 0.37/1.06    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.37/1.06    inference(ennf_transformation,[],[f11])).
% 0.37/1.06  
% 0.37/1.06  fof(f28,plain,(
% 0.37/1.06    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.37/1.06    inference(flattening,[],[f27])).
% 0.37/1.06  
% 0.37/1.06  fof(f38,plain,(
% 0.37/1.06    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/1.06    introduced(choice_axiom,[])).
% 0.37/1.06  
% 0.37/1.06  fof(f39,plain,(
% 0.37/1.06    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.37/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f38])).
% 0.37/1.06  
% 0.37/1.06  fof(f65,plain,(
% 0.37/1.06    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f39])).
% 0.37/1.06  
% 0.37/1.06  fof(f75,plain,(
% 0.37/1.06    ~v2_struct_0(sK3)),
% 0.37/1.06    inference(cnf_transformation,[],[f45])).
% 0.37/1.06  
% 0.37/1.06  fof(f3,axiom,(
% 0.37/1.06    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f18,plain,(
% 0.37/1.06    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.37/1.06    inference(ennf_transformation,[],[f3])).
% 0.37/1.06  
% 0.37/1.06  fof(f36,plain,(
% 0.37/1.06    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.37/1.06    inference(nnf_transformation,[],[f18])).
% 0.37/1.06  
% 0.37/1.06  fof(f48,plain,(
% 0.37/1.06    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f36])).
% 0.37/1.06  
% 0.37/1.06  fof(f12,axiom,(
% 0.37/1.06    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f17,plain,(
% 0.37/1.06    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.37/1.06    inference(rectify,[],[f12])).
% 0.37/1.06  
% 0.37/1.06  fof(f29,plain,(
% 0.37/1.06    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.37/1.06    inference(ennf_transformation,[],[f17])).
% 0.37/1.06  
% 0.37/1.06  fof(f40,plain,(
% 0.37/1.06    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)))),
% 0.37/1.06    introduced(choice_axiom,[])).
% 0.37/1.06  
% 0.37/1.06  fof(f41,plain,(
% 0.37/1.06    ! [X0] : (((r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.37/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f40])).
% 0.37/1.06  
% 0.37/1.06  fof(f67,plain,(
% 0.37/1.06    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 0.37/1.06    inference(cnf_transformation,[],[f41])).
% 0.37/1.06  
% 0.37/1.06  fof(f66,plain,(
% 0.37/1.06    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.37/1.06    inference(cnf_transformation,[],[f39])).
% 0.37/1.06  
% 0.37/1.06  fof(f1,axiom,(
% 0.37/1.06    v1_xboole_0(k1_xboole_0)),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f46,plain,(
% 0.37/1.06    v1_xboole_0(k1_xboole_0)),
% 0.37/1.06    inference(cnf_transformation,[],[f1])).
% 0.37/1.06  
% 0.37/1.06  fof(f2,axiom,(
% 0.37/1.06    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f47,plain,(
% 0.37/1.06    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.37/1.06    inference(cnf_transformation,[],[f2])).
% 0.37/1.06  
% 0.37/1.06  fof(f4,axiom,(
% 0.37/1.06    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.37/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.06  
% 0.37/1.06  fof(f52,plain,(
% 0.37/1.06    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.37/1.06    inference(cnf_transformation,[],[f4])).
% 0.37/1.06  
% 0.37/1.06  cnf(c_31,negated_conjecture,
% 0.37/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 0.37/1.06      inference(cnf_transformation,[],[f79]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1219,plain,
% 0.37/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_18,plain,
% 0.37/1.06      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f64]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_34,negated_conjecture,
% 0.37/1.06      ( l1_struct_0(sK3) ),
% 0.37/1.06      inference(cnf_transformation,[],[f76]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_403,plain,
% 0.37/1.06      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_404,plain,
% 0.37/1.06      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_403]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_36,negated_conjecture,
% 0.37/1.06      ( l1_struct_0(sK2) ),
% 0.37/1.06      inference(cnf_transformation,[],[f74]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_408,plain,
% 0.37/1.06      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_409,plain,
% 0.37/1.06      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_408]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1258,plain,
% 0.37/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) = iProver_top ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_1219,c_404,c_409]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_11,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f57]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1229,plain,
% 0.37/1.06      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1911,plain,
% 0.37/1.06      ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_1258,c_1229]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_30,negated_conjecture,
% 0.37/1.06      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 0.37/1.06      inference(cnf_transformation,[],[f80]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1255,plain,
% 0.37/1.06      ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_30,c_404,c_409]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2040,plain,
% 0.37/1.06      ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_1911,c_1255]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2437,plain,
% 0.37/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) = iProver_top ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_2040,c_1258]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_17,plain,
% 0.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | k1_relset_1(X1,X2,X0) = X1
% 0.37/1.06      | k1_xboole_0 = X2 ),
% 0.37/1.06      inference(cnf_transformation,[],[f58]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1223,plain,
% 0.37/1.06      ( k1_relset_1(X0,X1,X2) = X0
% 0.37/1.06      | k1_xboole_0 = X1
% 0.37/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 0.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_3382,plain,
% 0.37/1.06      ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_struct_0(sK2)
% 0.37/1.06      | k2_relat_1(sK4) = k1_xboole_0
% 0.37/1.06      | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_2437,c_1223]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_10,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f56]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1230,plain,
% 0.37/1.06      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2188,plain,
% 0.37/1.06      ( k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_1258,c_1230]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2724,plain,
% 0.37/1.06      ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_2188,c_2040]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_3386,plain,
% 0.37/1.06      ( k2_struct_0(sK2) = k1_relat_1(sK4)
% 0.37/1.06      | k2_relat_1(sK4) = k1_xboole_0
% 0.37/1.06      | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_3382,c_2724]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_32,negated_conjecture,
% 0.37/1.06      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 0.37/1.06      inference(cnf_transformation,[],[f78]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1218,plain,
% 0.37/1.06      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1252,plain,
% 0.37/1.06      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_1218,c_404,c_409]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2438,plain,
% 0.37/1.06      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) = iProver_top ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_2040,c_1252]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_3672,plain,
% 0.37/1.06      ( k2_relat_1(sK4) = k1_xboole_0
% 0.37/1.06      | k2_struct_0(sK2) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_3386,c_2438]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_3673,plain,
% 0.37/1.06      ( k2_struct_0(sK2) = k1_relat_1(sK4)
% 0.37/1.06      | k2_relat_1(sK4) = k1_xboole_0 ),
% 0.37/1.06      inference(renaming,[status(thm)],[c_3672]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_24,plain,
% 0.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | ~ v1_funct_1(X0)
% 0.37/1.06      | ~ v2_funct_1(X0)
% 0.37/1.06      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 0.37/1.06      | k2_relset_1(X1,X2,X0) != X2 ),
% 0.37/1.06      inference(cnf_transformation,[],[f70]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_29,negated_conjecture,
% 0.37/1.06      ( v2_funct_1(sK4) ),
% 0.37/1.06      inference(cnf_transformation,[],[f81]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_457,plain,
% 0.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | ~ v1_funct_1(X0)
% 0.37/1.06      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 0.37/1.06      | k2_relset_1(X1,X2,X0) != X2
% 0.37/1.06      | sK4 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_458,plain,
% 0.37/1.06      ( ~ v1_funct_2(sK4,X0,X1)
% 0.37/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.37/1.06      | ~ v1_funct_1(sK4)
% 0.37/1.06      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 0.37/1.06      | k2_relset_1(X0,X1,sK4) != X1 ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_457]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_33,negated_conjecture,
% 0.37/1.06      ( v1_funct_1(sK4) ),
% 0.37/1.06      inference(cnf_transformation,[],[f77]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_462,plain,
% 0.37/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.37/1.06      | ~ v1_funct_2(sK4,X0,X1)
% 0.37/1.06      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 0.37/1.06      | k2_relset_1(X0,X1,sK4) != X1 ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_458,c_33]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_463,plain,
% 0.37/1.06      ( ~ v1_funct_2(sK4,X0,X1)
% 0.37/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.37/1.06      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 0.37/1.06      | k2_relset_1(X0,X1,sK4) != X1 ),
% 0.37/1.06      inference(renaming,[status(thm)],[c_462]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1214,plain,
% 0.37/1.06      ( k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 0.37/1.06      | k2_relset_1(X0,X1,sK4) != X1
% 0.37/1.06      | v1_funct_2(sK4,X0,X1) != iProver_top
% 0.37/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1785,plain,
% 0.37/1.06      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
% 0.37/1.06      | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 0.37/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_1255,c_1214]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1788,plain,
% 0.37/1.06      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_1785,c_1258,c_1252]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2436,plain,
% 0.37/1.06      ( k2_tops_2(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_funct_1(sK4) ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_2040,c_1788]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_25,plain,
% 0.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 0.37/1.06      | ~ v1_funct_1(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f73]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1222,plain,
% 0.37/1.06      ( v1_funct_2(X0,X1,X2) != iProver_top
% 0.37/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.37/1.06      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 0.37/1.06      | v1_funct_1(X0) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4041,plain,
% 0.37/1.06      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top
% 0.37/1.06      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top
% 0.37/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) != iProver_top
% 0.37/1.06      | v1_funct_1(sK4) != iProver_top ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_2436,c_1222]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_40,plain,
% 0.37/1.06      ( v1_funct_1(sK4) = iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4372,plain,
% 0.37/1.06      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_4041,c_40,c_2437,c_2438]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4381,plain,
% 0.37/1.06      ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_4372,c_1229]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_9,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | v1_relat_1(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f55]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_7,plain,
% 0.37/1.06      ( ~ v1_relat_1(X0)
% 0.37/1.06      | ~ v1_funct_1(X0)
% 0.37/1.06      | ~ v2_funct_1(X0)
% 0.37/1.06      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f54]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_495,plain,
% 0.37/1.06      ( ~ v1_relat_1(X0)
% 0.37/1.06      | ~ v1_funct_1(X0)
% 0.37/1.06      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 0.37/1.06      | sK4 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_496,plain,
% 0.37/1.06      ( ~ v1_relat_1(sK4)
% 0.37/1.06      | ~ v1_funct_1(sK4)
% 0.37/1.06      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_495]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_498,plain,
% 0.37/1.06      ( ~ v1_relat_1(sK4)
% 0.37/1.06      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_496,c_33]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_520,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 0.37/1.06      | sK4 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_498]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_521,plain,
% 0.37/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.37/1.06      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_520]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1213,plain,
% 0.37/1.06      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 0.37/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1446,plain,
% 0.37/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.37/1.06      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_521]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1904,plain,
% 0.37/1.06      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_1213,c_31,c_1446]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4390,plain,
% 0.37/1.06      ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_4381,c_1904]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_28,negated_conjecture,
% 0.37/1.06      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 0.37/1.06      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
% 0.37/1.06      inference(cnf_transformation,[],[f82]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1349,plain,
% 0.37/1.06      ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 0.37/1.06      | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_28,c_404,c_409]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1791,plain,
% 0.37/1.06      ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
% 0.37/1.06      | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_1788,c_1349]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2435,plain,
% 0.37/1.06      ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
% 0.37/1.06      | k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4) ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_2040,c_1791]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4451,plain,
% 0.37/1.06      ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4)
% 0.37/1.06      | k2_struct_0(sK2) != k1_relat_1(sK4) ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_4390,c_2435]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4380,plain,
% 0.37/1.06      ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_4372,c_1230]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_8,plain,
% 0.37/1.06      ( ~ v1_relat_1(X0)
% 0.37/1.06      | ~ v1_funct_1(X0)
% 0.37/1.06      | ~ v2_funct_1(X0)
% 0.37/1.06      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f53]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_481,plain,
% 0.37/1.06      ( ~ v1_relat_1(X0)
% 0.37/1.06      | ~ v1_funct_1(X0)
% 0.37/1.06      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 0.37/1.06      | sK4 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_482,plain,
% 0.37/1.06      ( ~ v1_relat_1(sK4)
% 0.37/1.06      | ~ v1_funct_1(sK4)
% 0.37/1.06      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_481]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_484,plain,
% 0.37/1.06      ( ~ v1_relat_1(sK4)
% 0.37/1.06      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_482,c_33]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_532,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.06      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 0.37/1.06      | sK4 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_484]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_533,plain,
% 0.37/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.37/1.06      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_532]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1212,plain,
% 0.37/1.06      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 0.37/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1449,plain,
% 0.37/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.37/1.06      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_533]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1862,plain,
% 0.37/1.06      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_1212,c_31,c_1449]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4393,plain,
% 0.37/1.06      ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_4380,c_1862]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4567,plain,
% 0.37/1.06      ( k2_struct_0(sK2) != k1_relat_1(sK4) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_4451,c_4393]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4570,plain,
% 0.37/1.06      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 0.37/1.06      inference(superposition,[status(thm)],[c_3673,c_4567]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_20,plain,
% 0.37/1.06      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.37/1.06      | v2_struct_0(X0)
% 0.37/1.06      | ~ l1_struct_0(X0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f65]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_35,negated_conjecture,
% 0.37/1.06      ( ~ v2_struct_0(sK3) ),
% 0.37/1.06      inference(cnf_transformation,[],[f75]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_377,plain,
% 0.37/1.06      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.37/1.06      | ~ l1_struct_0(X0)
% 0.37/1.06      | sK3 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_378,plain,
% 0.37/1.06      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.37/1.06      | ~ l1_struct_0(sK3) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_377]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_380,plain,
% 0.37/1.06      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.37/1.06      inference(global_propositional_subsumption,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_378,c_34]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1216,plain,
% 0.37/1.06      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1249,plain,
% 0.37/1.06      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 0.37/1.06      inference(light_normalisation,[status(thm)],[c_1216,c_404]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2439,plain,
% 0.37/1.06      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_relat_1(sK4))) = iProver_top ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_2040,c_1249]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_4585,plain,
% 0.37/1.06      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 0.37/1.06      inference(demodulation,[status(thm)],[c_4570,c_2439]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_5,plain,
% 0.37/1.06      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 0.37/1.06      inference(cnf_transformation,[],[f48]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_23,plain,
% 0.37/1.06      ( ~ r2_hidden(X0,X1)
% 0.37/1.06      | k3_tarski(X1) != k1_xboole_0
% 0.37/1.06      | k1_xboole_0 = X0 ),
% 0.37/1.06      inference(cnf_transformation,[],[f67]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_550,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,X1)
% 0.37/1.06      | v1_xboole_0(X1)
% 0.37/1.06      | k3_tarski(X1) != k1_xboole_0
% 0.37/1.06      | k1_xboole_0 = X0 ),
% 0.37/1.06      inference(resolution,[status(thm)],[c_5,c_23]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1494,plain,
% 0.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.37/1.06      | v1_xboole_0(k1_zfmisc_1(X1))
% 0.37/1.06      | k3_tarski(k1_zfmisc_1(X1)) != k1_xboole_0
% 0.37/1.06      | k1_xboole_0 = X0 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_550]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2596,plain,
% 0.37/1.06      ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(X0))
% 0.37/1.06      | v1_xboole_0(k1_zfmisc_1(X0))
% 0.37/1.06      | k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
% 0.37/1.06      | k1_xboole_0 = sK0(sK3) ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_1494]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2603,plain,
% 0.37/1.06      ( k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
% 0.37/1.06      | k1_xboole_0 = sK0(sK3)
% 0.37/1.06      | m1_subset_1(sK0(sK3),k1_zfmisc_1(X0)) != iProver_top
% 0.37/1.06      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_2596]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_2605,plain,
% 0.37/1.06      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
% 0.37/1.06      | k1_xboole_0 = sK0(sK3)
% 0.37/1.06      | m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 0.37/1.06      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_2603]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_765,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1628,plain,
% 0.37/1.06      ( X0 != X1 | sK0(sK3) != X1 | sK0(sK3) = X0 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_765]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1888,plain,
% 0.37/1.06      ( X0 != sK0(sK3) | sK0(sK3) = X0 | sK0(sK3) != sK0(sK3) ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_1628]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1890,plain,
% 0.37/1.06      ( sK0(sK3) != sK0(sK3)
% 0.37/1.06      | sK0(sK3) = k1_xboole_0
% 0.37/1.06      | k1_xboole_0 != sK0(sK3) ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_1888]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_764,plain,( X0 = X0 ),theory(equality) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1886,plain,
% 0.37/1.06      ( sK3 = sK3 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_764]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_780,plain,( X0 != X1 | sK0(X0) = sK0(X1) ),theory(equality) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1630,plain,
% 0.37/1.06      ( sK0(sK3) = sK0(X0) | sK3 != X0 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_780]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1885,plain,
% 0.37/1.06      ( sK0(sK3) = sK0(sK3) | sK3 != sK3 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_1630]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_766,plain,
% 0.37/1.06      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.37/1.06      theory(equality) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1480,plain,
% 0.37/1.06      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0(sK3)) | sK0(sK3) != X0 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_766]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1482,plain,
% 0.37/1.06      ( v1_xboole_0(sK0(sK3))
% 0.37/1.06      | ~ v1_xboole_0(k1_xboole_0)
% 0.37/1.06      | sK0(sK3) != k1_xboole_0 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_1480]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_19,plain,
% 0.37/1.06      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(sK0(X0)) ),
% 0.37/1.06      inference(cnf_transformation,[],[f66]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_388,plain,
% 0.37/1.06      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(sK0(X0)) | sK3 != X0 ),
% 0.37/1.06      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_389,plain,
% 0.37/1.06      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(sK0(sK3)) ),
% 0.37/1.06      inference(unflattening,[status(thm)],[c_388]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_0,plain,
% 0.37/1.06      ( v1_xboole_0(k1_xboole_0) ),
% 0.37/1.06      inference(cnf_transformation,[],[f46]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_1,plain,
% 0.37/1.06      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 0.37/1.06      inference(cnf_transformation,[],[f47]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_118,plain,
% 0.37/1.06      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_1]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_6,plain,
% 0.37/1.06      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 0.37/1.06      inference(cnf_transformation,[],[f52]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_105,plain,
% 0.37/1.06      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 0.37/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(c_107,plain,
% 0.37/1.06      ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.37/1.06      inference(instantiation,[status(thm)],[c_105]) ).
% 0.37/1.06  
% 0.37/1.06  cnf(contradiction,plain,
% 0.37/1.06      ( $false ),
% 0.37/1.06      inference(minisat,
% 0.37/1.06                [status(thm)],
% 0.37/1.06                [c_4585,c_2605,c_1890,c_1886,c_1885,c_1482,c_389,c_0,
% 0.37/1.06                 c_118,c_107,c_34]) ).
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.06  
% 0.37/1.06  ------                               Statistics
% 0.37/1.06  
% 0.37/1.06  ------ General
% 0.37/1.06  
% 0.37/1.06  abstr_ref_over_cycles:                  0
% 0.37/1.06  abstr_ref_under_cycles:                 0
% 0.37/1.06  gc_basic_clause_elim:                   0
% 0.37/1.06  forced_gc_time:                         0
% 0.37/1.06  parsing_time:                           0.009
% 0.37/1.06  unif_index_cands_time:                  0.
% 0.37/1.06  unif_index_add_time:                    0.
% 0.37/1.06  orderings_time:                         0.
% 0.37/1.06  out_proof_time:                         0.01
% 0.37/1.06  total_time:                             0.166
% 0.37/1.06  num_of_symbols:                         57
% 0.37/1.06  num_of_terms:                           3943
% 0.37/1.06  
% 0.37/1.06  ------ Preprocessing
% 0.37/1.06  
% 0.37/1.06  num_of_splits:                          0
% 0.37/1.06  num_of_split_atoms:                     0
% 0.37/1.06  num_of_reused_defs:                     0
% 0.37/1.06  num_eq_ax_congr_red:                    7
% 0.37/1.06  num_of_sem_filtered_clauses:            1
% 0.37/1.06  num_of_subtypes:                        0
% 0.37/1.06  monotx_restored_types:                  0
% 0.37/1.06  sat_num_of_epr_types:                   0
% 0.37/1.06  sat_num_of_non_cyclic_types:            0
% 0.37/1.06  sat_guarded_non_collapsed_types:        0
% 0.37/1.06  num_pure_diseq_elim:                    0
% 0.37/1.06  simp_replaced_by:                       0
% 0.37/1.06  res_preprocessed:                       167
% 0.37/1.06  prep_upred:                             0
% 0.37/1.06  prep_unflattend:                        13
% 0.37/1.06  smt_new_axioms:                         0
% 0.37/1.06  pred_elim_cands:                        4
% 0.37/1.06  pred_elim:                              5
% 0.37/1.06  pred_elim_cl:                           6
% 0.37/1.06  pred_elim_cycles:                       8
% 0.37/1.06  merged_defs:                            0
% 0.37/1.06  merged_defs_ncl:                        0
% 0.37/1.06  bin_hyper_res:                          0
% 0.37/1.06  prep_cycles:                            4
% 0.37/1.06  pred_elim_time:                         0.005
% 0.37/1.06  splitting_time:                         0.
% 0.37/1.06  sem_filter_time:                        0.
% 0.37/1.06  monotx_time:                            0.001
% 0.37/1.06  subtype_inf_time:                       0.
% 0.37/1.06  
% 0.37/1.06  ------ Problem properties
% 0.37/1.06  
% 0.37/1.06  clauses:                                31
% 0.37/1.06  conjectures:                            5
% 0.37/1.06  epr:                                    4
% 0.37/1.06  horn:                                   25
% 0.37/1.06  ground:                                 10
% 0.37/1.06  unary:                                  11
% 0.37/1.06  binary:                                 6
% 0.37/1.06  lits:                                   73
% 0.37/1.06  lits_eq:                                26
% 0.37/1.06  fd_pure:                                0
% 0.37/1.06  fd_pseudo:                              0
% 0.37/1.06  fd_cond:                                4
% 0.37/1.06  fd_pseudo_cond:                         0
% 0.37/1.06  ac_symbols:                             0
% 0.37/1.06  
% 0.37/1.06  ------ Propositional Solver
% 0.37/1.06  
% 0.37/1.06  prop_solver_calls:                      28
% 0.37/1.06  prop_fast_solver_calls:                 1020
% 0.37/1.06  smt_solver_calls:                       0
% 0.37/1.06  smt_fast_solver_calls:                  0
% 0.37/1.06  prop_num_of_clauses:                    1541
% 0.37/1.06  prop_preprocess_simplified:             5719
% 0.37/1.06  prop_fo_subsumed:                       23
% 0.37/1.06  prop_solver_time:                       0.
% 0.37/1.06  smt_solver_time:                        0.
% 0.37/1.06  smt_fast_solver_time:                   0.
% 0.37/1.06  prop_fast_solver_time:                  0.
% 0.37/1.06  prop_unsat_core_time:                   0.
% 0.37/1.06  
% 0.37/1.06  ------ QBF
% 0.37/1.06  
% 0.37/1.06  qbf_q_res:                              0
% 0.37/1.06  qbf_num_tautologies:                    0
% 0.37/1.06  qbf_prep_cycles:                        0
% 0.37/1.06  
% 0.37/1.06  ------ BMC1
% 0.37/1.06  
% 0.37/1.06  bmc1_current_bound:                     -1
% 0.37/1.06  bmc1_last_solved_bound:                 -1
% 0.37/1.06  bmc1_unsat_core_size:                   -1
% 0.37/1.06  bmc1_unsat_core_parents_size:           -1
% 0.37/1.06  bmc1_merge_next_fun:                    0
% 0.37/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.37/1.06  
% 0.37/1.06  ------ Instantiation
% 0.37/1.06  
% 0.37/1.06  inst_num_of_clauses:                    519
% 0.37/1.06  inst_num_in_passive:                    175
% 0.37/1.06  inst_num_in_active:                     254
% 0.37/1.06  inst_num_in_unprocessed:                90
% 0.37/1.06  inst_num_of_loops:                      280
% 0.37/1.06  inst_num_of_learning_restarts:          0
% 0.37/1.06  inst_num_moves_active_passive:          23
% 0.37/1.06  inst_lit_activity:                      0
% 0.37/1.06  inst_lit_activity_moves:                0
% 0.37/1.06  inst_num_tautologies:                   0
% 0.37/1.06  inst_num_prop_implied:                  0
% 0.37/1.06  inst_num_existing_simplified:           0
% 0.37/1.06  inst_num_eq_res_simplified:             0
% 0.37/1.06  inst_num_child_elim:                    0
% 0.37/1.06  inst_num_of_dismatching_blockings:      143
% 0.37/1.06  inst_num_of_non_proper_insts:           452
% 0.37/1.06  inst_num_of_duplicates:                 0
% 0.37/1.06  inst_inst_num_from_inst_to_res:         0
% 0.37/1.06  inst_dismatching_checking_time:         0.
% 0.37/1.06  
% 0.37/1.06  ------ Resolution
% 0.37/1.06  
% 0.37/1.06  res_num_of_clauses:                     0
% 0.37/1.06  res_num_in_passive:                     0
% 0.37/1.06  res_num_in_active:                      0
% 0.37/1.06  res_num_of_loops:                       171
% 0.37/1.06  res_forward_subset_subsumed:            52
% 0.37/1.06  res_backward_subset_subsumed:           4
% 0.37/1.06  res_forward_subsumed:                   0
% 0.37/1.06  res_backward_subsumed:                  0
% 0.37/1.06  res_forward_subsumption_resolution:     0
% 0.37/1.06  res_backward_subsumption_resolution:    0
% 0.37/1.06  res_clause_to_clause_subsumption:       130
% 0.37/1.06  res_orphan_elimination:                 0
% 0.37/1.06  res_tautology_del:                      26
% 0.37/1.06  res_num_eq_res_simplified:              0
% 0.37/1.06  res_num_sel_changes:                    0
% 0.37/1.06  res_moves_from_active_to_pass:          0
% 0.37/1.06  
% 0.37/1.06  ------ Superposition
% 0.37/1.06  
% 0.37/1.06  sup_time_total:                         0.
% 0.37/1.06  sup_time_generating:                    0.
% 0.37/1.06  sup_time_sim_full:                      0.
% 0.37/1.06  sup_time_sim_immed:                     0.
% 0.37/1.06  
% 0.37/1.06  sup_num_of_clauses:                     56
% 0.37/1.06  sup_num_in_active:                      29
% 0.37/1.06  sup_num_in_passive:                     27
% 0.37/1.06  sup_num_of_loops:                       55
% 0.37/1.06  sup_fw_superposition:                   27
% 0.37/1.06  sup_bw_superposition:                   34
% 0.37/1.06  sup_immediate_simplified:               30
% 0.37/1.06  sup_given_eliminated:                   0
% 0.37/1.06  comparisons_done:                       0
% 0.37/1.06  comparisons_avoided:                    12
% 0.37/1.06  
% 0.37/1.06  ------ Simplifications
% 0.37/1.06  
% 0.37/1.06  
% 0.37/1.06  sim_fw_subset_subsumed:                 6
% 0.37/1.06  sim_bw_subset_subsumed:                 5
% 0.37/1.06  sim_fw_subsumed:                        13
% 0.37/1.06  sim_bw_subsumed:                        0
% 0.37/1.06  sim_fw_subsumption_res:                 3
% 0.37/1.06  sim_bw_subsumption_res:                 0
% 0.37/1.06  sim_tautology_del:                      2
% 0.37/1.06  sim_eq_tautology_del:                   1
% 0.37/1.06  sim_eq_res_simp:                        0
% 0.37/1.06  sim_fw_demodulated:                     6
% 0.37/1.06  sim_bw_demodulated:                     25
% 0.37/1.06  sim_light_normalised:                   11
% 0.37/1.06  sim_joinable_taut:                      0
% 0.37/1.06  sim_joinable_simp:                      0
% 0.37/1.06  sim_ac_normalised:                      0
% 0.37/1.06  sim_smt_subsumption:                    0
% 0.37/1.06  
%------------------------------------------------------------------------------
