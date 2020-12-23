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
% DateTime   : Thu Dec  3 12:17:16 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  151 (6304 expanded)
%              Number of clauses        :   93 (1745 expanded)
%              Number of leaves         :   16 (1907 expanded)
%              Depth                    :   22
%              Number of atoms          :  458 (45542 expanded)
%              Number of equality atoms :  218 (15910 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35,f34,f33])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_915,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_333,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_334,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_338,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_339,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_947,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_915,c_334,c_339])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_925,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1364,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_947,c_925])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_944,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_22,c_334,c_339])).

cnf(c_1545,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1364,c_944])).

cnf(c_1551,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1545,c_947])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_919,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2603,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_919])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_926,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2241,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1551,c_926])).

cnf(c_2604,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2603,c_2241])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_914,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_941,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_914,c_334,c_339])).

cnf(c_1552,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1545,c_941])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_306,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_324,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_27])).

cnf(c_325,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_327,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_26])).

cnf(c_1554,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1545,c_327])).

cnf(c_2978,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_1552,c_1554])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_930,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2239,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_930])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1115,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1317,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1318,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_2314,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2239,c_34,c_1241,c_1318])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_369,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_370,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_372,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_25])).

cnf(c_911,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_2321,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2314,c_911])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_345,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_346,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_25])).

cnf(c_351,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_912,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_1370,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_912])).

cnf(c_1428,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1370,c_947,c_941])).

cnf(c_1550,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1545,c_1428])).

cnf(c_2431,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2321,c_1550])).

cnf(c_2983,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2978,c_2431])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_918,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3658,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_918])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2985,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2978,c_1551])).

cnf(c_2987,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2978,c_1552])).

cnf(c_4294,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3658,c_32,c_2985,c_2987])).

cnf(c_4305,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4294,c_926])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_927,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2320,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2314,c_927])).

cnf(c_4310,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4305,c_2320])).

cnf(c_3052,plain,
    ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_925])).

cnf(c_3630,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_3052])).

cnf(c_4170,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3630,c_32,c_2987])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_928,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2319,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2314,c_928])).

cnf(c_4172,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4170,c_2319,c_2983])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1018,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_20,c_334,c_339])).

cnf(c_1431,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1428,c_1018])).

cnf(c_1549,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1545,c_1431])).

cnf(c_2430,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2321,c_1549])).

cnf(c_2982,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2978,c_2430])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4310,c_4172,c_2982])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.56/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/0.99  
% 2.56/0.99  ------  iProver source info
% 2.56/0.99  
% 2.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/0.99  git: non_committed_changes: false
% 2.56/0.99  git: last_make_outside_of_git: false
% 2.56/0.99  
% 2.56/0.99  ------ 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options
% 2.56/0.99  
% 2.56/0.99  --out_options                           all
% 2.56/0.99  --tptp_safe_out                         true
% 2.56/0.99  --problem_path                          ""
% 2.56/0.99  --include_path                          ""
% 2.56/0.99  --clausifier                            res/vclausify_rel
% 2.56/0.99  --clausifier_options                    --mode clausify
% 2.56/0.99  --stdin                                 false
% 2.56/0.99  --stats_out                             all
% 2.56/0.99  
% 2.56/0.99  ------ General Options
% 2.56/0.99  
% 2.56/0.99  --fof                                   false
% 2.56/0.99  --time_out_real                         305.
% 2.56/0.99  --time_out_virtual                      -1.
% 2.56/0.99  --symbol_type_check                     false
% 2.56/0.99  --clausify_out                          false
% 2.56/0.99  --sig_cnt_out                           false
% 2.56/1.00  --trig_cnt_out                          false
% 2.56/1.00  --trig_cnt_out_tolerance                1.
% 2.56/1.00  --trig_cnt_out_sk_spl                   false
% 2.56/1.00  --abstr_cl_out                          false
% 2.56/1.00  
% 2.56/1.00  ------ Global Options
% 2.56/1.00  
% 2.56/1.00  --schedule                              default
% 2.56/1.00  --add_important_lit                     false
% 2.56/1.00  --prop_solver_per_cl                    1000
% 2.56/1.00  --min_unsat_core                        false
% 2.56/1.00  --soft_assumptions                      false
% 2.56/1.00  --soft_lemma_size                       3
% 2.56/1.00  --prop_impl_unit_size                   0
% 2.56/1.00  --prop_impl_unit                        []
% 2.56/1.00  --share_sel_clauses                     true
% 2.56/1.00  --reset_solvers                         false
% 2.56/1.00  --bc_imp_inh                            [conj_cone]
% 2.56/1.00  --conj_cone_tolerance                   3.
% 2.56/1.00  --extra_neg_conj                        none
% 2.56/1.00  --large_theory_mode                     true
% 2.56/1.00  --prolific_symb_bound                   200
% 2.56/1.00  --lt_threshold                          2000
% 2.56/1.00  --clause_weak_htbl                      true
% 2.56/1.00  --gc_record_bc_elim                     false
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing Options
% 2.56/1.00  
% 2.56/1.00  --preprocessing_flag                    true
% 2.56/1.00  --time_out_prep_mult                    0.1
% 2.56/1.00  --splitting_mode                        input
% 2.56/1.00  --splitting_grd                         true
% 2.56/1.00  --splitting_cvd                         false
% 2.56/1.00  --splitting_cvd_svl                     false
% 2.56/1.00  --splitting_nvd                         32
% 2.56/1.00  --sub_typing                            true
% 2.56/1.00  --prep_gs_sim                           true
% 2.56/1.00  --prep_unflatten                        true
% 2.56/1.00  --prep_res_sim                          true
% 2.56/1.00  --prep_upred                            true
% 2.56/1.00  --prep_sem_filter                       exhaustive
% 2.56/1.00  --prep_sem_filter_out                   false
% 2.56/1.00  --pred_elim                             true
% 2.56/1.00  --res_sim_input                         true
% 2.56/1.00  --eq_ax_congr_red                       true
% 2.56/1.00  --pure_diseq_elim                       true
% 2.56/1.00  --brand_transform                       false
% 2.56/1.00  --non_eq_to_eq                          false
% 2.56/1.00  --prep_def_merge                        true
% 2.56/1.00  --prep_def_merge_prop_impl              false
% 2.56/1.00  --prep_def_merge_mbd                    true
% 2.56/1.00  --prep_def_merge_tr_red                 false
% 2.56/1.00  --prep_def_merge_tr_cl                  false
% 2.56/1.00  --smt_preprocessing                     true
% 2.56/1.00  --smt_ac_axioms                         fast
% 2.56/1.00  --preprocessed_out                      false
% 2.56/1.00  --preprocessed_stats                    false
% 2.56/1.00  
% 2.56/1.00  ------ Abstraction refinement Options
% 2.56/1.00  
% 2.56/1.00  --abstr_ref                             []
% 2.56/1.00  --abstr_ref_prep                        false
% 2.56/1.00  --abstr_ref_until_sat                   false
% 2.56/1.00  --abstr_ref_sig_restrict                funpre
% 2.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.00  --abstr_ref_under                       []
% 2.56/1.00  
% 2.56/1.00  ------ SAT Options
% 2.56/1.00  
% 2.56/1.00  --sat_mode                              false
% 2.56/1.00  --sat_fm_restart_options                ""
% 2.56/1.00  --sat_gr_def                            false
% 2.56/1.00  --sat_epr_types                         true
% 2.56/1.00  --sat_non_cyclic_types                  false
% 2.56/1.00  --sat_finite_models                     false
% 2.56/1.00  --sat_fm_lemmas                         false
% 2.56/1.00  --sat_fm_prep                           false
% 2.56/1.00  --sat_fm_uc_incr                        true
% 2.56/1.00  --sat_out_model                         small
% 2.56/1.00  --sat_out_clauses                       false
% 2.56/1.00  
% 2.56/1.00  ------ QBF Options
% 2.56/1.00  
% 2.56/1.00  --qbf_mode                              false
% 2.56/1.00  --qbf_elim_univ                         false
% 2.56/1.00  --qbf_dom_inst                          none
% 2.56/1.00  --qbf_dom_pre_inst                      false
% 2.56/1.00  --qbf_sk_in                             false
% 2.56/1.00  --qbf_pred_elim                         true
% 2.56/1.00  --qbf_split                             512
% 2.56/1.00  
% 2.56/1.00  ------ BMC1 Options
% 2.56/1.00  
% 2.56/1.00  --bmc1_incremental                      false
% 2.56/1.00  --bmc1_axioms                           reachable_all
% 2.56/1.00  --bmc1_min_bound                        0
% 2.56/1.00  --bmc1_max_bound                        -1
% 2.56/1.00  --bmc1_max_bound_default                -1
% 2.56/1.00  --bmc1_symbol_reachability              true
% 2.56/1.00  --bmc1_property_lemmas                  false
% 2.56/1.00  --bmc1_k_induction                      false
% 2.56/1.00  --bmc1_non_equiv_states                 false
% 2.56/1.00  --bmc1_deadlock                         false
% 2.56/1.00  --bmc1_ucm                              false
% 2.56/1.00  --bmc1_add_unsat_core                   none
% 2.56/1.00  --bmc1_unsat_core_children              false
% 2.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.00  --bmc1_out_stat                         full
% 2.56/1.00  --bmc1_ground_init                      false
% 2.56/1.00  --bmc1_pre_inst_next_state              false
% 2.56/1.00  --bmc1_pre_inst_state                   false
% 2.56/1.00  --bmc1_pre_inst_reach_state             false
% 2.56/1.00  --bmc1_out_unsat_core                   false
% 2.56/1.00  --bmc1_aig_witness_out                  false
% 2.56/1.00  --bmc1_verbose                          false
% 2.56/1.00  --bmc1_dump_clauses_tptp                false
% 2.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.00  --bmc1_dump_file                        -
% 2.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.00  --bmc1_ucm_extend_mode                  1
% 2.56/1.00  --bmc1_ucm_init_mode                    2
% 2.56/1.00  --bmc1_ucm_cone_mode                    none
% 2.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.00  --bmc1_ucm_relax_model                  4
% 2.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.00  --bmc1_ucm_layered_model                none
% 2.56/1.00  --bmc1_ucm_max_lemma_size               10
% 2.56/1.00  
% 2.56/1.00  ------ AIG Options
% 2.56/1.00  
% 2.56/1.00  --aig_mode                              false
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation Options
% 2.56/1.00  
% 2.56/1.00  --instantiation_flag                    true
% 2.56/1.00  --inst_sos_flag                         false
% 2.56/1.00  --inst_sos_phase                        true
% 2.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel_side                     num_symb
% 2.56/1.00  --inst_solver_per_active                1400
% 2.56/1.00  --inst_solver_calls_frac                1.
% 2.56/1.00  --inst_passive_queue_type               priority_queues
% 2.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.00  --inst_passive_queues_freq              [25;2]
% 2.56/1.00  --inst_dismatching                      true
% 2.56/1.00  --inst_eager_unprocessed_to_passive     true
% 2.56/1.00  --inst_prop_sim_given                   true
% 2.56/1.00  --inst_prop_sim_new                     false
% 2.56/1.00  --inst_subs_new                         false
% 2.56/1.00  --inst_eq_res_simp                      false
% 2.56/1.00  --inst_subs_given                       false
% 2.56/1.00  --inst_orphan_elimination               true
% 2.56/1.00  --inst_learning_loop_flag               true
% 2.56/1.00  --inst_learning_start                   3000
% 2.56/1.00  --inst_learning_factor                  2
% 2.56/1.00  --inst_start_prop_sim_after_learn       3
% 2.56/1.00  --inst_sel_renew                        solver
% 2.56/1.00  --inst_lit_activity_flag                true
% 2.56/1.00  --inst_restr_to_given                   false
% 2.56/1.00  --inst_activity_threshold               500
% 2.56/1.00  --inst_out_proof                        true
% 2.56/1.00  
% 2.56/1.00  ------ Resolution Options
% 2.56/1.00  
% 2.56/1.00  --resolution_flag                       true
% 2.56/1.00  --res_lit_sel                           adaptive
% 2.56/1.00  --res_lit_sel_side                      none
% 2.56/1.00  --res_ordering                          kbo
% 2.56/1.00  --res_to_prop_solver                    active
% 2.56/1.00  --res_prop_simpl_new                    false
% 2.56/1.00  --res_prop_simpl_given                  true
% 2.56/1.00  --res_passive_queue_type                priority_queues
% 2.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.00  --res_passive_queues_freq               [15;5]
% 2.56/1.00  --res_forward_subs                      full
% 2.56/1.00  --res_backward_subs                     full
% 2.56/1.00  --res_forward_subs_resolution           true
% 2.56/1.00  --res_backward_subs_resolution          true
% 2.56/1.00  --res_orphan_elimination                true
% 2.56/1.00  --res_time_limit                        2.
% 2.56/1.00  --res_out_proof                         true
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Options
% 2.56/1.00  
% 2.56/1.00  --superposition_flag                    true
% 2.56/1.00  --sup_passive_queue_type                priority_queues
% 2.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.00  --demod_completeness_check              fast
% 2.56/1.00  --demod_use_ground                      true
% 2.56/1.00  --sup_to_prop_solver                    passive
% 2.56/1.00  --sup_prop_simpl_new                    true
% 2.56/1.00  --sup_prop_simpl_given                  true
% 2.56/1.00  --sup_fun_splitting                     false
% 2.56/1.00  --sup_smt_interval                      50000
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Simplification Setup
% 2.56/1.00  
% 2.56/1.00  --sup_indices_passive                   []
% 2.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_full_bw                           [BwDemod]
% 2.56/1.00  --sup_immed_triv                        [TrivRules]
% 2.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_immed_bw_main                     []
% 2.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  
% 2.56/1.00  ------ Combination Options
% 2.56/1.00  
% 2.56/1.00  --comb_res_mult                         3
% 2.56/1.00  --comb_sup_mult                         2
% 2.56/1.00  --comb_inst_mult                        10
% 2.56/1.00  
% 2.56/1.00  ------ Debug Options
% 2.56/1.00  
% 2.56/1.00  --dbg_backtrace                         false
% 2.56/1.00  --dbg_dump_prop_clauses                 false
% 2.56/1.00  --dbg_dump_prop_clauses_file            -
% 2.56/1.00  --dbg_out_stat                          false
% 2.56/1.00  ------ Parsing...
% 2.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.00  ------ Proving...
% 2.56/1.00  ------ Problem Properties 
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  clauses                                 25
% 2.56/1.00  conjectures                             5
% 2.56/1.00  EPR                                     1
% 2.56/1.00  Horn                                    21
% 2.56/1.00  unary                                   8
% 2.56/1.00  binary                                  6
% 2.56/1.00  lits                                    60
% 2.56/1.00  lits eq                                 22
% 2.56/1.00  fd_pure                                 0
% 2.56/1.00  fd_pseudo                               0
% 2.56/1.00  fd_cond                                 3
% 2.56/1.00  fd_pseudo_cond                          0
% 2.56/1.00  AC symbols                              0
% 2.56/1.00  
% 2.56/1.00  ------ Schedule dynamic 5 is on 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  ------ 
% 2.56/1.00  Current options:
% 2.56/1.00  ------ 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options
% 2.56/1.00  
% 2.56/1.00  --out_options                           all
% 2.56/1.00  --tptp_safe_out                         true
% 2.56/1.00  --problem_path                          ""
% 2.56/1.00  --include_path                          ""
% 2.56/1.00  --clausifier                            res/vclausify_rel
% 2.56/1.00  --clausifier_options                    --mode clausify
% 2.56/1.00  --stdin                                 false
% 2.56/1.00  --stats_out                             all
% 2.56/1.00  
% 2.56/1.00  ------ General Options
% 2.56/1.00  
% 2.56/1.00  --fof                                   false
% 2.56/1.00  --time_out_real                         305.
% 2.56/1.00  --time_out_virtual                      -1.
% 2.56/1.00  --symbol_type_check                     false
% 2.56/1.00  --clausify_out                          false
% 2.56/1.00  --sig_cnt_out                           false
% 2.56/1.00  --trig_cnt_out                          false
% 2.56/1.00  --trig_cnt_out_tolerance                1.
% 2.56/1.00  --trig_cnt_out_sk_spl                   false
% 2.56/1.00  --abstr_cl_out                          false
% 2.56/1.00  
% 2.56/1.00  ------ Global Options
% 2.56/1.00  
% 2.56/1.00  --schedule                              default
% 2.56/1.00  --add_important_lit                     false
% 2.56/1.00  --prop_solver_per_cl                    1000
% 2.56/1.00  --min_unsat_core                        false
% 2.56/1.00  --soft_assumptions                      false
% 2.56/1.00  --soft_lemma_size                       3
% 2.56/1.00  --prop_impl_unit_size                   0
% 2.56/1.00  --prop_impl_unit                        []
% 2.56/1.00  --share_sel_clauses                     true
% 2.56/1.00  --reset_solvers                         false
% 2.56/1.00  --bc_imp_inh                            [conj_cone]
% 2.56/1.00  --conj_cone_tolerance                   3.
% 2.56/1.00  --extra_neg_conj                        none
% 2.56/1.00  --large_theory_mode                     true
% 2.56/1.00  --prolific_symb_bound                   200
% 2.56/1.00  --lt_threshold                          2000
% 2.56/1.00  --clause_weak_htbl                      true
% 2.56/1.00  --gc_record_bc_elim                     false
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing Options
% 2.56/1.00  
% 2.56/1.00  --preprocessing_flag                    true
% 2.56/1.00  --time_out_prep_mult                    0.1
% 2.56/1.00  --splitting_mode                        input
% 2.56/1.00  --splitting_grd                         true
% 2.56/1.00  --splitting_cvd                         false
% 2.56/1.00  --splitting_cvd_svl                     false
% 2.56/1.00  --splitting_nvd                         32
% 2.56/1.00  --sub_typing                            true
% 2.56/1.00  --prep_gs_sim                           true
% 2.56/1.00  --prep_unflatten                        true
% 2.56/1.00  --prep_res_sim                          true
% 2.56/1.00  --prep_upred                            true
% 2.56/1.00  --prep_sem_filter                       exhaustive
% 2.56/1.00  --prep_sem_filter_out                   false
% 2.56/1.00  --pred_elim                             true
% 2.56/1.00  --res_sim_input                         true
% 2.56/1.00  --eq_ax_congr_red                       true
% 2.56/1.00  --pure_diseq_elim                       true
% 2.56/1.00  --brand_transform                       false
% 2.56/1.00  --non_eq_to_eq                          false
% 2.56/1.00  --prep_def_merge                        true
% 2.56/1.00  --prep_def_merge_prop_impl              false
% 2.56/1.00  --prep_def_merge_mbd                    true
% 2.56/1.00  --prep_def_merge_tr_red                 false
% 2.56/1.00  --prep_def_merge_tr_cl                  false
% 2.56/1.00  --smt_preprocessing                     true
% 2.56/1.00  --smt_ac_axioms                         fast
% 2.56/1.00  --preprocessed_out                      false
% 2.56/1.00  --preprocessed_stats                    false
% 2.56/1.00  
% 2.56/1.00  ------ Abstraction refinement Options
% 2.56/1.00  
% 2.56/1.00  --abstr_ref                             []
% 2.56/1.00  --abstr_ref_prep                        false
% 2.56/1.00  --abstr_ref_until_sat                   false
% 2.56/1.00  --abstr_ref_sig_restrict                funpre
% 2.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.00  --abstr_ref_under                       []
% 2.56/1.00  
% 2.56/1.00  ------ SAT Options
% 2.56/1.00  
% 2.56/1.00  --sat_mode                              false
% 2.56/1.00  --sat_fm_restart_options                ""
% 2.56/1.00  --sat_gr_def                            false
% 2.56/1.00  --sat_epr_types                         true
% 2.56/1.00  --sat_non_cyclic_types                  false
% 2.56/1.00  --sat_finite_models                     false
% 2.56/1.00  --sat_fm_lemmas                         false
% 2.56/1.00  --sat_fm_prep                           false
% 2.56/1.00  --sat_fm_uc_incr                        true
% 2.56/1.00  --sat_out_model                         small
% 2.56/1.00  --sat_out_clauses                       false
% 2.56/1.00  
% 2.56/1.00  ------ QBF Options
% 2.56/1.00  
% 2.56/1.00  --qbf_mode                              false
% 2.56/1.00  --qbf_elim_univ                         false
% 2.56/1.00  --qbf_dom_inst                          none
% 2.56/1.00  --qbf_dom_pre_inst                      false
% 2.56/1.00  --qbf_sk_in                             false
% 2.56/1.00  --qbf_pred_elim                         true
% 2.56/1.00  --qbf_split                             512
% 2.56/1.00  
% 2.56/1.00  ------ BMC1 Options
% 2.56/1.00  
% 2.56/1.00  --bmc1_incremental                      false
% 2.56/1.00  --bmc1_axioms                           reachable_all
% 2.56/1.00  --bmc1_min_bound                        0
% 2.56/1.00  --bmc1_max_bound                        -1
% 2.56/1.00  --bmc1_max_bound_default                -1
% 2.56/1.00  --bmc1_symbol_reachability              true
% 2.56/1.00  --bmc1_property_lemmas                  false
% 2.56/1.00  --bmc1_k_induction                      false
% 2.56/1.00  --bmc1_non_equiv_states                 false
% 2.56/1.00  --bmc1_deadlock                         false
% 2.56/1.00  --bmc1_ucm                              false
% 2.56/1.00  --bmc1_add_unsat_core                   none
% 2.56/1.00  --bmc1_unsat_core_children              false
% 2.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.00  --bmc1_out_stat                         full
% 2.56/1.00  --bmc1_ground_init                      false
% 2.56/1.00  --bmc1_pre_inst_next_state              false
% 2.56/1.00  --bmc1_pre_inst_state                   false
% 2.56/1.00  --bmc1_pre_inst_reach_state             false
% 2.56/1.00  --bmc1_out_unsat_core                   false
% 2.56/1.00  --bmc1_aig_witness_out                  false
% 2.56/1.00  --bmc1_verbose                          false
% 2.56/1.00  --bmc1_dump_clauses_tptp                false
% 2.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.00  --bmc1_dump_file                        -
% 2.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.00  --bmc1_ucm_extend_mode                  1
% 2.56/1.00  --bmc1_ucm_init_mode                    2
% 2.56/1.00  --bmc1_ucm_cone_mode                    none
% 2.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.00  --bmc1_ucm_relax_model                  4
% 2.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.00  --bmc1_ucm_layered_model                none
% 2.56/1.00  --bmc1_ucm_max_lemma_size               10
% 2.56/1.00  
% 2.56/1.00  ------ AIG Options
% 2.56/1.00  
% 2.56/1.00  --aig_mode                              false
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation Options
% 2.56/1.00  
% 2.56/1.00  --instantiation_flag                    true
% 2.56/1.00  --inst_sos_flag                         false
% 2.56/1.00  --inst_sos_phase                        true
% 2.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel_side                     none
% 2.56/1.00  --inst_solver_per_active                1400
% 2.56/1.00  --inst_solver_calls_frac                1.
% 2.56/1.00  --inst_passive_queue_type               priority_queues
% 2.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.00  --inst_passive_queues_freq              [25;2]
% 2.56/1.00  --inst_dismatching                      true
% 2.56/1.00  --inst_eager_unprocessed_to_passive     true
% 2.56/1.00  --inst_prop_sim_given                   true
% 2.56/1.00  --inst_prop_sim_new                     false
% 2.56/1.00  --inst_subs_new                         false
% 2.56/1.00  --inst_eq_res_simp                      false
% 2.56/1.00  --inst_subs_given                       false
% 2.56/1.00  --inst_orphan_elimination               true
% 2.56/1.00  --inst_learning_loop_flag               true
% 2.56/1.00  --inst_learning_start                   3000
% 2.56/1.00  --inst_learning_factor                  2
% 2.56/1.00  --inst_start_prop_sim_after_learn       3
% 2.56/1.00  --inst_sel_renew                        solver
% 2.56/1.00  --inst_lit_activity_flag                true
% 2.56/1.00  --inst_restr_to_given                   false
% 2.56/1.00  --inst_activity_threshold               500
% 2.56/1.00  --inst_out_proof                        true
% 2.56/1.00  
% 2.56/1.00  ------ Resolution Options
% 2.56/1.00  
% 2.56/1.00  --resolution_flag                       false
% 2.56/1.00  --res_lit_sel                           adaptive
% 2.56/1.00  --res_lit_sel_side                      none
% 2.56/1.00  --res_ordering                          kbo
% 2.56/1.00  --res_to_prop_solver                    active
% 2.56/1.00  --res_prop_simpl_new                    false
% 2.56/1.00  --res_prop_simpl_given                  true
% 2.56/1.00  --res_passive_queue_type                priority_queues
% 2.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.00  --res_passive_queues_freq               [15;5]
% 2.56/1.00  --res_forward_subs                      full
% 2.56/1.00  --res_backward_subs                     full
% 2.56/1.00  --res_forward_subs_resolution           true
% 2.56/1.00  --res_backward_subs_resolution          true
% 2.56/1.00  --res_orphan_elimination                true
% 2.56/1.00  --res_time_limit                        2.
% 2.56/1.00  --res_out_proof                         true
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Options
% 2.56/1.00  
% 2.56/1.00  --superposition_flag                    true
% 2.56/1.00  --sup_passive_queue_type                priority_queues
% 2.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.00  --demod_completeness_check              fast
% 2.56/1.00  --demod_use_ground                      true
% 2.56/1.00  --sup_to_prop_solver                    passive
% 2.56/1.00  --sup_prop_simpl_new                    true
% 2.56/1.00  --sup_prop_simpl_given                  true
% 2.56/1.00  --sup_fun_splitting                     false
% 2.56/1.00  --sup_smt_interval                      50000
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Simplification Setup
% 2.56/1.00  
% 2.56/1.00  --sup_indices_passive                   []
% 2.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_full_bw                           [BwDemod]
% 2.56/1.00  --sup_immed_triv                        [TrivRules]
% 2.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_immed_bw_main                     []
% 2.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  
% 2.56/1.00  ------ Combination Options
% 2.56/1.00  
% 2.56/1.00  --comb_res_mult                         3
% 2.56/1.00  --comb_sup_mult                         2
% 2.56/1.00  --comb_inst_mult                        10
% 2.56/1.00  
% 2.56/1.00  ------ Debug Options
% 2.56/1.00  
% 2.56/1.00  --dbg_backtrace                         false
% 2.56/1.00  --dbg_dump_prop_clauses                 false
% 2.56/1.00  --dbg_dump_prop_clauses_file            -
% 2.56/1.00  --dbg_out_stat                          false
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  ------ Proving...
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  % SZS status Theorem for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  fof(f13,conjecture,(
% 2.56/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f14,negated_conjecture,(
% 2.56/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.56/1.00    inference(negated_conjecture,[],[f13])).
% 2.56/1.00  
% 2.56/1.00  fof(f30,plain,(
% 2.56/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f14])).
% 2.56/1.00  
% 2.56/1.00  fof(f31,plain,(
% 2.56/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.56/1.00    inference(flattening,[],[f30])).
% 2.56/1.00  
% 2.56/1.00  fof(f35,plain,(
% 2.56/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f34,plain,(
% 2.56/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f33,plain,(
% 2.56/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f36,plain,(
% 2.56/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35,f34,f33])).
% 2.56/1.00  
% 2.56/1.00  fof(f62,plain,(
% 2.56/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f9,axiom,(
% 2.56/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f23,plain,(
% 2.56/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f9])).
% 2.56/1.00  
% 2.56/1.00  fof(f51,plain,(
% 2.56/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f23])).
% 2.56/1.00  
% 2.56/1.00  fof(f59,plain,(
% 2.56/1.00    l1_struct_0(sK1)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f57,plain,(
% 2.56/1.00    l1_struct_0(sK0)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f7,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f20,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f7])).
% 2.56/1.00  
% 2.56/1.00  fof(f44,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f20])).
% 2.56/1.00  
% 2.56/1.00  fof(f63,plain,(
% 2.56/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f8,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f21,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f8])).
% 2.56/1.00  
% 2.56/1.00  fof(f22,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(flattening,[],[f21])).
% 2.56/1.00  
% 2.56/1.00  fof(f32,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(nnf_transformation,[],[f22])).
% 2.56/1.00  
% 2.56/1.00  fof(f45,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f32])).
% 2.56/1.00  
% 2.56/1.00  fof(f6,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f19,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f6])).
% 2.56/1.00  
% 2.56/1.00  fof(f43,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f19])).
% 2.56/1.00  
% 2.56/1.00  fof(f61,plain,(
% 2.56/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f1,axiom,(
% 2.56/1.00    v1_xboole_0(k1_xboole_0)),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f37,plain,(
% 2.56/1.00    v1_xboole_0(k1_xboole_0)),
% 2.56/1.00    inference(cnf_transformation,[],[f1])).
% 2.56/1.00  
% 2.56/1.00  fof(f10,axiom,(
% 2.56/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f24,plain,(
% 2.56/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.56/1.00    inference(ennf_transformation,[],[f10])).
% 2.56/1.00  
% 2.56/1.00  fof(f25,plain,(
% 2.56/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.56/1.00    inference(flattening,[],[f24])).
% 2.56/1.00  
% 2.56/1.00  fof(f52,plain,(
% 2.56/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f25])).
% 2.56/1.00  
% 2.56/1.00  fof(f58,plain,(
% 2.56/1.00    ~v2_struct_0(sK1)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f2,axiom,(
% 2.56/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f15,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f2])).
% 2.56/1.00  
% 2.56/1.00  fof(f38,plain,(
% 2.56/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f15])).
% 2.56/1.00  
% 2.56/1.00  fof(f3,axiom,(
% 2.56/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f39,plain,(
% 2.56/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f3])).
% 2.56/1.00  
% 2.56/1.00  fof(f5,axiom,(
% 2.56/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f17,plain,(
% 2.56/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/1.00    inference(ennf_transformation,[],[f5])).
% 2.56/1.00  
% 2.56/1.00  fof(f18,plain,(
% 2.56/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/1.00    inference(flattening,[],[f17])).
% 2.56/1.00  
% 2.56/1.00  fof(f42,plain,(
% 2.56/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f18])).
% 2.56/1.00  
% 2.56/1.00  fof(f64,plain,(
% 2.56/1.00    v2_funct_1(sK2)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f60,plain,(
% 2.56/1.00    v1_funct_1(sK2)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f11,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f26,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/1.00    inference(ennf_transformation,[],[f11])).
% 2.56/1.00  
% 2.56/1.00  fof(f27,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/1.00    inference(flattening,[],[f26])).
% 2.56/1.00  
% 2.56/1.00  fof(f53,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f27])).
% 2.56/1.00  
% 2.56/1.00  fof(f12,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f28,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/1.00    inference(ennf_transformation,[],[f12])).
% 2.56/1.00  
% 2.56/1.00  fof(f29,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/1.00    inference(flattening,[],[f28])).
% 2.56/1.00  
% 2.56/1.00  fof(f56,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f29])).
% 2.56/1.00  
% 2.56/1.00  fof(f4,axiom,(
% 2.56/1.00    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f16,plain,(
% 2.56/1.00    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f4])).
% 2.56/1.00  
% 2.56/1.00  fof(f40,plain,(
% 2.56/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f16])).
% 2.56/1.00  
% 2.56/1.00  fof(f41,plain,(
% 2.56/1.00    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f16])).
% 2.56/1.00  
% 2.56/1.00  fof(f65,plain,(
% 2.56/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  cnf(c_23,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_915,plain,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_14,plain,
% 2.56/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_26,negated_conjecture,
% 2.56/1.00      ( l1_struct_0(sK1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_333,plain,
% 2.56/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_334,plain,
% 2.56/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_333]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_28,negated_conjecture,
% 2.56/1.00      ( l1_struct_0(sK0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_338,plain,
% 2.56/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_339,plain,
% 2.56/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_947,plain,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_915,c_334,c_339]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_7,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_925,plain,
% 2.56/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.56/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1364,plain,
% 2.56/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_947,c_925]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_22,negated_conjecture,
% 2.56/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_944,plain,
% 2.56/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_22,c_334,c_339]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1545,plain,
% 2.56/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1364,c_944]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1551,plain,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1545,c_947]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_13,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.56/1.00      | k1_xboole_0 = X2 ),
% 2.56/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_919,plain,
% 2.56/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 2.56/1.00      | k1_xboole_0 = X1
% 2.56/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.56/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2603,plain,
% 2.56/1.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 2.56/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.56/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1551,c_919]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_6,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_926,plain,
% 2.56/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.56/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2241,plain,
% 2.56/1.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1551,c_926]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2604,plain,
% 2.56/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.56/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.56/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_2603,c_2241]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_24,negated_conjecture,
% 2.56/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.56/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_914,plain,
% 2.56/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_941,plain,
% 2.56/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_914,c_334,c_339]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1552,plain,
% 2.56/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1545,c_941]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_0,plain,
% 2.56/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_15,plain,
% 2.56/1.00      ( v2_struct_0(X0)
% 2.56/1.00      | ~ l1_struct_0(X0)
% 2.56/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.56/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_306,plain,
% 2.56/1.00      ( v2_struct_0(X0)
% 2.56/1.00      | ~ l1_struct_0(X0)
% 2.56/1.00      | k2_struct_0(X0) != k1_xboole_0 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_27,negated_conjecture,
% 2.56/1.00      ( ~ v2_struct_0(sK1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_324,plain,
% 2.56/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_306,c_27]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_325,plain,
% 2.56/1.00      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_327,plain,
% 2.56/1.00      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_325,c_26]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1554,plain,
% 2.56/1.00      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1545,c_327]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2978,plain,
% 2.56/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_2604,c_1552,c_1554]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/1.00      | ~ v1_relat_1(X1)
% 2.56/1.00      | v1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_930,plain,
% 2.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.56/1.00      | v1_relat_1(X1) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2239,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 2.56/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1551,c_930]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_34,plain,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1115,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | v1_relat_1(X0)
% 2.56/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.56/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1240,plain,
% 2.56/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.56/1.00      | v1_relat_1(sK2) ),
% 2.56/1.00      inference(instantiation,[status(thm)],[c_1115]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1241,plain,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.56/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.56/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1317,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.56/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1318,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2314,plain,
% 2.56/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_2239,c_34,c_1241,c_1318]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5,plain,
% 2.56/1.00      ( ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v2_funct_1(X0)
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_21,negated_conjecture,
% 2.56/1.00      ( v2_funct_1(sK2) ),
% 2.56/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_369,plain,
% 2.56/1.00      ( ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.56/1.00      | sK2 != X0 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_370,plain,
% 2.56/1.00      ( ~ v1_funct_1(sK2)
% 2.56/1.00      | ~ v1_relat_1(sK2)
% 2.56/1.00      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_369]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_25,negated_conjecture,
% 2.56/1.00      ( v1_funct_1(sK2) ),
% 2.56/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_372,plain,
% 2.56/1.00      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_370,c_25]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_911,plain,
% 2.56/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.56/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2321,plain,
% 2.56/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2314,c_911]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_16,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v2_funct_1(X0)
% 2.56/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.56/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_345,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.56/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.56/1.00      | sK2 != X0 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_346,plain,
% 2.56/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.56/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.56/1.00      | ~ v1_funct_1(sK2)
% 2.56/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.56/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_350,plain,
% 2.56/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.56/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.56/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.56/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_346,c_25]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_351,plain,
% 2.56/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.56/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.56/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.56/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_350]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_912,plain,
% 2.56/1.00      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.56/1.00      | k2_relset_1(X0,X1,sK2) != X1
% 2.56/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.56/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1370,plain,
% 2.56/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.56/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.56/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_944,c_912]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1428,plain,
% 2.56/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_1370,c_947,c_941]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1550,plain,
% 2.56/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1545,c_1428]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2431,plain,
% 2.56/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2321,c_1550]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2983,plain,
% 2.56/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2978,c_2431]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_17,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.56/1.00      | ~ v1_funct_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_918,plain,
% 2.56/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.56/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.56/1.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3658,plain,
% 2.56/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.56/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2983,c_918]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_32,plain,
% 2.56/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2985,plain,
% 2.56/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2978,c_1551]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2987,plain,
% 2.56/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2978,c_1552]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4294,plain,
% 2.56/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_3658,c_32,c_2985,c_2987]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4305,plain,
% 2.56/1.00      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_4294,c_926]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4,plain,
% 2.56/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_927,plain,
% 2.56/1.00      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 2.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2320,plain,
% 2.56/1.00      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2314,c_927]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4310,plain,
% 2.56/1.00      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_4305,c_2320]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3052,plain,
% 2.56/1.00      ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
% 2.56/1.00      | v1_funct_2(X2,X1,X0) != iProver_top
% 2.56/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.56/1.00      | v1_funct_1(X2) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_918,c_925]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3630,plain,
% 2.56/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
% 2.56/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2985,c_3052]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4170,plain,
% 2.56/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_3630,c_32,c_2987]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3,plain,
% 2.56/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_928,plain,
% 2.56/1.00      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 2.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2319,plain,
% 2.56/1.00      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2314,c_928]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4172,plain,
% 2.56/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_4170,c_2319,c_2983]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_20,negated_conjecture,
% 2.56/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.56/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1018,plain,
% 2.56/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.56/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_20,c_334,c_339]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1431,plain,
% 2.56/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.56/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1428,c_1018]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1549,plain,
% 2.56/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.56/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1545,c_1431]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2430,plain,
% 2.56/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_struct_0(sK0)
% 2.56/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2321,c_1549]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2982,plain,
% 2.56/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2)
% 2.56/1.00      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2978,c_2430]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(contradiction,plain,
% 2.56/1.00      ( $false ),
% 2.56/1.00      inference(minisat,[status(thm)],[c_4310,c_4172,c_2982]) ).
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  ------                               Statistics
% 2.56/1.00  
% 2.56/1.00  ------ General
% 2.56/1.00  
% 2.56/1.00  abstr_ref_over_cycles:                  0
% 2.56/1.00  abstr_ref_under_cycles:                 0
% 2.56/1.00  gc_basic_clause_elim:                   0
% 2.56/1.00  forced_gc_time:                         0
% 2.56/1.00  parsing_time:                           0.007
% 2.56/1.00  unif_index_cands_time:                  0.
% 2.56/1.00  unif_index_add_time:                    0.
% 2.56/1.00  orderings_time:                         0.
% 2.56/1.00  out_proof_time:                         0.014
% 2.56/1.00  total_time:                             0.154
% 2.56/1.00  num_of_symbols:                         54
% 2.56/1.00  num_of_terms:                           4332
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing
% 2.56/1.00  
% 2.56/1.00  num_of_splits:                          0
% 2.56/1.00  num_of_split_atoms:                     0
% 2.56/1.00  num_of_reused_defs:                     0
% 2.56/1.00  num_eq_ax_congr_red:                    2
% 2.56/1.00  num_of_sem_filtered_clauses:            1
% 2.56/1.00  num_of_subtypes:                        0
% 2.56/1.00  monotx_restored_types:                  0
% 2.56/1.00  sat_num_of_epr_types:                   0
% 2.56/1.00  sat_num_of_non_cyclic_types:            0
% 2.56/1.00  sat_guarded_non_collapsed_types:        0
% 2.56/1.00  num_pure_diseq_elim:                    0
% 2.56/1.00  simp_replaced_by:                       0
% 2.56/1.00  res_preprocessed:                       139
% 2.56/1.00  prep_upred:                             0
% 2.56/1.00  prep_unflattend:                        5
% 2.56/1.00  smt_new_axioms:                         0
% 2.56/1.00  pred_elim_cands:                        4
% 2.56/1.00  pred_elim:                              4
% 2.56/1.00  pred_elim_cl:                           4
% 2.56/1.00  pred_elim_cycles:                       6
% 2.56/1.00  merged_defs:                            0
% 2.56/1.00  merged_defs_ncl:                        0
% 2.56/1.00  bin_hyper_res:                          0
% 2.56/1.00  prep_cycles:                            4
% 2.56/1.00  pred_elim_time:                         0.001
% 2.56/1.00  splitting_time:                         0.
% 2.56/1.00  sem_filter_time:                        0.
% 2.56/1.00  monotx_time:                            0.
% 2.56/1.00  subtype_inf_time:                       0.
% 2.56/1.00  
% 2.56/1.00  ------ Problem properties
% 2.56/1.00  
% 2.56/1.00  clauses:                                25
% 2.56/1.00  conjectures:                            5
% 2.56/1.00  epr:                                    1
% 2.56/1.00  horn:                                   21
% 2.56/1.00  ground:                                 9
% 2.56/1.00  unary:                                  8
% 2.56/1.00  binary:                                 6
% 2.56/1.00  lits:                                   60
% 2.56/1.00  lits_eq:                                22
% 2.56/1.00  fd_pure:                                0
% 2.56/1.00  fd_pseudo:                              0
% 2.56/1.00  fd_cond:                                3
% 2.56/1.00  fd_pseudo_cond:                         0
% 2.56/1.00  ac_symbols:                             0
% 2.56/1.00  
% 2.56/1.00  ------ Propositional Solver
% 2.56/1.00  
% 2.56/1.00  prop_solver_calls:                      28
% 2.56/1.00  prop_fast_solver_calls:                 864
% 2.56/1.00  smt_solver_calls:                       0
% 2.56/1.00  smt_fast_solver_calls:                  0
% 2.56/1.00  prop_num_of_clauses:                    1308
% 2.56/1.00  prop_preprocess_simplified:             4846
% 2.56/1.00  prop_fo_subsumed:                       20
% 2.56/1.00  prop_solver_time:                       0.
% 2.56/1.00  smt_solver_time:                        0.
% 2.56/1.00  smt_fast_solver_time:                   0.
% 2.56/1.00  prop_fast_solver_time:                  0.
% 2.56/1.00  prop_unsat_core_time:                   0.
% 2.56/1.00  
% 2.56/1.00  ------ QBF
% 2.56/1.00  
% 2.56/1.00  qbf_q_res:                              0
% 2.56/1.00  qbf_num_tautologies:                    0
% 2.56/1.00  qbf_prep_cycles:                        0
% 2.56/1.00  
% 2.56/1.00  ------ BMC1
% 2.56/1.00  
% 2.56/1.00  bmc1_current_bound:                     -1
% 2.56/1.00  bmc1_last_solved_bound:                 -1
% 2.56/1.00  bmc1_unsat_core_size:                   -1
% 2.56/1.00  bmc1_unsat_core_parents_size:           -1
% 2.56/1.00  bmc1_merge_next_fun:                    0
% 2.56/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation
% 2.56/1.00  
% 2.56/1.00  inst_num_of_clauses:                    475
% 2.56/1.00  inst_num_in_passive:                    57
% 2.56/1.00  inst_num_in_active:                     297
% 2.56/1.00  inst_num_in_unprocessed:                121
% 2.56/1.00  inst_num_of_loops:                      310
% 2.56/1.00  inst_num_of_learning_restarts:          0
% 2.56/1.00  inst_num_moves_active_passive:          9
% 2.56/1.00  inst_lit_activity:                      0
% 2.56/1.00  inst_lit_activity_moves:                0
% 2.56/1.00  inst_num_tautologies:                   0
% 2.56/1.00  inst_num_prop_implied:                  0
% 2.56/1.00  inst_num_existing_simplified:           0
% 2.56/1.00  inst_num_eq_res_simplified:             0
% 2.56/1.00  inst_num_child_elim:                    0
% 2.56/1.00  inst_num_of_dismatching_blockings:      120
% 2.56/1.00  inst_num_of_non_proper_insts:           395
% 2.56/1.00  inst_num_of_duplicates:                 0
% 2.56/1.00  inst_inst_num_from_inst_to_res:         0
% 2.56/1.00  inst_dismatching_checking_time:         0.
% 2.56/1.00  
% 2.56/1.00  ------ Resolution
% 2.56/1.00  
% 2.56/1.00  res_num_of_clauses:                     0
% 2.56/1.00  res_num_in_passive:                     0
% 2.56/1.00  res_num_in_active:                      0
% 2.56/1.00  res_num_of_loops:                       143
% 2.56/1.00  res_forward_subset_subsumed:            44
% 2.56/1.00  res_backward_subset_subsumed:           2
% 2.56/1.00  res_forward_subsumed:                   0
% 2.56/1.00  res_backward_subsumed:                  0
% 2.56/1.00  res_forward_subsumption_resolution:     0
% 2.56/1.00  res_backward_subsumption_resolution:    0
% 2.56/1.00  res_clause_to_clause_subsumption:       102
% 2.56/1.00  res_orphan_elimination:                 0
% 2.56/1.00  res_tautology_del:                      57
% 2.56/1.00  res_num_eq_res_simplified:              0
% 2.56/1.00  res_num_sel_changes:                    0
% 2.56/1.00  res_moves_from_active_to_pass:          0
% 2.56/1.00  
% 2.56/1.00  ------ Superposition
% 2.56/1.00  
% 2.56/1.00  sup_time_total:                         0.
% 2.56/1.00  sup_time_generating:                    0.
% 2.56/1.00  sup_time_sim_full:                      0.
% 2.56/1.00  sup_time_sim_immed:                     0.
% 2.56/1.00  
% 2.56/1.00  sup_num_of_clauses:                     56
% 2.56/1.00  sup_num_in_active:                      40
% 2.56/1.00  sup_num_in_passive:                     16
% 2.56/1.00  sup_num_of_loops:                       61
% 2.56/1.00  sup_fw_superposition:                   11
% 2.56/1.00  sup_bw_superposition:                   36
% 2.56/1.00  sup_immediate_simplified:               15
% 2.56/1.00  sup_given_eliminated:                   0
% 2.56/1.00  comparisons_done:                       0
% 2.56/1.00  comparisons_avoided:                    0
% 2.56/1.00  
% 2.56/1.00  ------ Simplifications
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  sim_fw_subset_subsumed:                 10
% 2.56/1.00  sim_bw_subset_subsumed:                 1
% 2.56/1.00  sim_fw_subsumed:                        0
% 2.56/1.00  sim_bw_subsumed:                        0
% 2.56/1.00  sim_fw_subsumption_res:                 1
% 2.56/1.00  sim_bw_subsumption_res:                 0
% 2.56/1.00  sim_tautology_del:                      0
% 2.56/1.00  sim_eq_tautology_del:                   1
% 2.56/1.00  sim_eq_res_simp:                        0
% 2.56/1.00  sim_fw_demodulated:                     0
% 2.56/1.00  sim_bw_demodulated:                     21
% 2.56/1.00  sim_light_normalised:                   12
% 2.56/1.00  sim_joinable_taut:                      0
% 2.56/1.00  sim_joinable_simp:                      0
% 2.56/1.00  sim_ac_normalised:                      0
% 2.56/1.00  sim_smt_subsumption:                    0
% 2.56/1.00  
%------------------------------------------------------------------------------
