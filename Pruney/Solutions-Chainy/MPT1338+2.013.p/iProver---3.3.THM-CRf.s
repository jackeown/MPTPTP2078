%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:01 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  190 (43066 expanded)
%              Number of clauses        :  121 (11700 expanded)
%              Number of leaves         :   16 (12843 expanded)
%              Depth                    :   28
%              Number of atoms          :  629 (311496 expanded)
%              Number of equality atoms :  302 (106043 expanded)
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f38,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_xboole_0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1155,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_349,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_350,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_354,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_355,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1181,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1155,c_350,c_355])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1165,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1605,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1181,c_1165])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1178,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_25,c_350,c_355])).

cnf(c_1869,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1605,c_1178])).

cnf(c_1876,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1869,c_1181])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_336,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_337,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_339,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_29])).

cnf(c_361,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_339])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_384,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_5,c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_16,c_5,c_4])).

cnf(c_389,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_362,c_389])).

cnf(c_1152,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1291,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1152,c_350])).

cnf(c_1784,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1291])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1154,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1175,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1154,c_350,c_355])).

cnf(c_2798,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1784,c_35,c_1175])).

cnf(c_2799,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2798])).

cnf(c_2806,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1876,c_2799])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1159,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2866,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_1159])).

cnf(c_1877,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1869,c_1175])).

cnf(c_3259,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2866,c_1877])).

cnf(c_3260,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3259])).

cnf(c_3395,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2806,c_3260])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1410,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_456,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_457,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_461,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_28])).

cnf(c_462,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_1151,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_1611,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1151])).

cnf(c_1731,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1611,c_1181,c_1175])).

cnf(c_23,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1254,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_23,c_350,c_355])).

cnf(c_1734,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1731,c_1254])).

cnf(c_1874,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1869,c_1734])).

cnf(c_3396,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2806,c_1874])).

cnf(c_3397,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2806,c_1876])).

cnf(c_3400,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2806,c_1877])).

cnf(c_1875,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1869,c_1731])).

cnf(c_3398,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2806,c_1875])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1157,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3622,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_1157])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1158,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3064,plain,
    ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1165])).

cnf(c_3937,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3397,c_3064])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_494,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_495,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_497,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_28])).

cnf(c_1149,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_1406,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_28,c_26,c_495,c_1359])).

cnf(c_3941,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3937,c_1406,c_3398])).

cnf(c_3059,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1158])).

cnf(c_4151,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3059,c_35,c_1876,c_1877])).

cnf(c_4155,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4151,c_2806])).

cnf(c_4161,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4155,c_1159])).

cnf(c_4290,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3395,c_35,c_26,c_1359,c_1410,c_3396,c_3397,c_3400,c_3622,c_3941,c_4161])).

cnf(c_4298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4290,c_3397])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_480,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_481,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_483,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_28])).

cnf(c_1150,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1459,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1150,c_28,c_26,c_481,c_1359])).

cnf(c_1167,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1548,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_1167])).

cnf(c_1549,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1548,c_1406])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1411,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2553,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1549,c_26,c_1359,c_1411])).

cnf(c_2554,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2553])).

cnf(c_4303,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4290,c_2554])).

cnf(c_4313,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4303])).

cnf(c_4335,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4298,c_4313])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1160,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3065,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1160])).

cnf(c_5293,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3065,c_1157])).

cnf(c_6764,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,sK2)) = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4335,c_5293])).

cnf(c_4300,plain,
    ( k2_tops_2(k1_relat_1(sK2),k1_xboole_0,sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4290,c_3398])).

cnf(c_4329,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4300,c_4313])).

cnf(c_6790,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6764,c_4329])).

cnf(c_4237,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3396,c_35,c_3400,c_3941])).

cnf(c_4294,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK2),k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4290,c_4237])).

cnf(c_4347,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4294,c_4313])).

cnf(c_4301,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4290,c_3400])).

cnf(c_4326,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4301,c_4313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6790,c_4347,c_4326,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.22/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.01  
% 3.22/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/1.01  
% 3.22/1.01  ------  iProver source info
% 3.22/1.01  
% 3.22/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.22/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/1.01  git: non_committed_changes: false
% 3.22/1.01  git: last_make_outside_of_git: false
% 3.22/1.01  
% 3.22/1.01  ------ 
% 3.22/1.01  
% 3.22/1.01  ------ Input Options
% 3.22/1.01  
% 3.22/1.01  --out_options                           all
% 3.22/1.01  --tptp_safe_out                         true
% 3.22/1.01  --problem_path                          ""
% 3.22/1.01  --include_path                          ""
% 3.22/1.01  --clausifier                            res/vclausify_rel
% 3.22/1.01  --clausifier_options                    --mode clausify
% 3.22/1.01  --stdin                                 false
% 3.22/1.01  --stats_out                             all
% 3.22/1.01  
% 3.22/1.01  ------ General Options
% 3.22/1.01  
% 3.22/1.01  --fof                                   false
% 3.22/1.01  --time_out_real                         305.
% 3.22/1.01  --time_out_virtual                      -1.
% 3.22/1.01  --symbol_type_check                     false
% 3.22/1.01  --clausify_out                          false
% 3.22/1.01  --sig_cnt_out                           false
% 3.22/1.01  --trig_cnt_out                          false
% 3.22/1.01  --trig_cnt_out_tolerance                1.
% 3.22/1.01  --trig_cnt_out_sk_spl                   false
% 3.22/1.01  --abstr_cl_out                          false
% 3.22/1.01  
% 3.22/1.01  ------ Global Options
% 3.22/1.01  
% 3.22/1.01  --schedule                              default
% 3.22/1.01  --add_important_lit                     false
% 3.22/1.01  --prop_solver_per_cl                    1000
% 3.22/1.01  --min_unsat_core                        false
% 3.22/1.01  --soft_assumptions                      false
% 3.22/1.01  --soft_lemma_size                       3
% 3.22/1.01  --prop_impl_unit_size                   0
% 3.22/1.01  --prop_impl_unit                        []
% 3.22/1.01  --share_sel_clauses                     true
% 3.22/1.01  --reset_solvers                         false
% 3.22/1.01  --bc_imp_inh                            [conj_cone]
% 3.22/1.01  --conj_cone_tolerance                   3.
% 3.22/1.01  --extra_neg_conj                        none
% 3.22/1.01  --large_theory_mode                     true
% 3.22/1.01  --prolific_symb_bound                   200
% 3.22/1.01  --lt_threshold                          2000
% 3.22/1.01  --clause_weak_htbl                      true
% 3.22/1.01  --gc_record_bc_elim                     false
% 3.22/1.01  
% 3.22/1.01  ------ Preprocessing Options
% 3.22/1.01  
% 3.22/1.01  --preprocessing_flag                    true
% 3.22/1.01  --time_out_prep_mult                    0.1
% 3.22/1.01  --splitting_mode                        input
% 3.22/1.01  --splitting_grd                         true
% 3.22/1.01  --splitting_cvd                         false
% 3.22/1.01  --splitting_cvd_svl                     false
% 3.22/1.01  --splitting_nvd                         32
% 3.22/1.01  --sub_typing                            true
% 3.22/1.01  --prep_gs_sim                           true
% 3.22/1.01  --prep_unflatten                        true
% 3.22/1.01  --prep_res_sim                          true
% 3.22/1.01  --prep_upred                            true
% 3.22/1.01  --prep_sem_filter                       exhaustive
% 3.22/1.01  --prep_sem_filter_out                   false
% 3.22/1.01  --pred_elim                             true
% 3.22/1.01  --res_sim_input                         true
% 3.22/1.01  --eq_ax_congr_red                       true
% 3.22/1.01  --pure_diseq_elim                       true
% 3.22/1.01  --brand_transform                       false
% 3.22/1.01  --non_eq_to_eq                          false
% 3.22/1.01  --prep_def_merge                        true
% 3.22/1.01  --prep_def_merge_prop_impl              false
% 3.22/1.01  --prep_def_merge_mbd                    true
% 3.22/1.01  --prep_def_merge_tr_red                 false
% 3.22/1.01  --prep_def_merge_tr_cl                  false
% 3.22/1.01  --smt_preprocessing                     true
% 3.22/1.01  --smt_ac_axioms                         fast
% 3.22/1.01  --preprocessed_out                      false
% 3.22/1.01  --preprocessed_stats                    false
% 3.22/1.01  
% 3.22/1.01  ------ Abstraction refinement Options
% 3.22/1.01  
% 3.22/1.01  --abstr_ref                             []
% 3.22/1.01  --abstr_ref_prep                        false
% 3.22/1.01  --abstr_ref_until_sat                   false
% 3.22/1.01  --abstr_ref_sig_restrict                funpre
% 3.22/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.01  --abstr_ref_under                       []
% 3.22/1.01  
% 3.22/1.01  ------ SAT Options
% 3.22/1.01  
% 3.22/1.01  --sat_mode                              false
% 3.22/1.01  --sat_fm_restart_options                ""
% 3.22/1.01  --sat_gr_def                            false
% 3.22/1.01  --sat_epr_types                         true
% 3.22/1.01  --sat_non_cyclic_types                  false
% 3.22/1.01  --sat_finite_models                     false
% 3.22/1.01  --sat_fm_lemmas                         false
% 3.22/1.01  --sat_fm_prep                           false
% 3.22/1.01  --sat_fm_uc_incr                        true
% 3.22/1.01  --sat_out_model                         small
% 3.22/1.01  --sat_out_clauses                       false
% 3.22/1.01  
% 3.22/1.01  ------ QBF Options
% 3.22/1.01  
% 3.22/1.01  --qbf_mode                              false
% 3.22/1.01  --qbf_elim_univ                         false
% 3.22/1.01  --qbf_dom_inst                          none
% 3.22/1.01  --qbf_dom_pre_inst                      false
% 3.22/1.01  --qbf_sk_in                             false
% 3.22/1.01  --qbf_pred_elim                         true
% 3.22/1.01  --qbf_split                             512
% 3.22/1.01  
% 3.22/1.01  ------ BMC1 Options
% 3.22/1.01  
% 3.22/1.01  --bmc1_incremental                      false
% 3.22/1.01  --bmc1_axioms                           reachable_all
% 3.22/1.01  --bmc1_min_bound                        0
% 3.22/1.01  --bmc1_max_bound                        -1
% 3.22/1.01  --bmc1_max_bound_default                -1
% 3.22/1.01  --bmc1_symbol_reachability              true
% 3.22/1.01  --bmc1_property_lemmas                  false
% 3.22/1.01  --bmc1_k_induction                      false
% 3.22/1.01  --bmc1_non_equiv_states                 false
% 3.22/1.01  --bmc1_deadlock                         false
% 3.22/1.01  --bmc1_ucm                              false
% 3.22/1.01  --bmc1_add_unsat_core                   none
% 3.22/1.01  --bmc1_unsat_core_children              false
% 3.22/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.01  --bmc1_out_stat                         full
% 3.22/1.01  --bmc1_ground_init                      false
% 3.22/1.01  --bmc1_pre_inst_next_state              false
% 3.22/1.01  --bmc1_pre_inst_state                   false
% 3.22/1.01  --bmc1_pre_inst_reach_state             false
% 3.22/1.01  --bmc1_out_unsat_core                   false
% 3.22/1.01  --bmc1_aig_witness_out                  false
% 3.22/1.01  --bmc1_verbose                          false
% 3.22/1.01  --bmc1_dump_clauses_tptp                false
% 3.22/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.01  --bmc1_dump_file                        -
% 3.22/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.01  --bmc1_ucm_extend_mode                  1
% 3.22/1.01  --bmc1_ucm_init_mode                    2
% 3.22/1.01  --bmc1_ucm_cone_mode                    none
% 3.22/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.01  --bmc1_ucm_relax_model                  4
% 3.22/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.01  --bmc1_ucm_layered_model                none
% 3.22/1.01  --bmc1_ucm_max_lemma_size               10
% 3.22/1.01  
% 3.22/1.01  ------ AIG Options
% 3.22/1.01  
% 3.22/1.01  --aig_mode                              false
% 3.22/1.01  
% 3.22/1.01  ------ Instantiation Options
% 3.22/1.01  
% 3.22/1.01  --instantiation_flag                    true
% 3.22/1.01  --inst_sos_flag                         false
% 3.22/1.01  --inst_sos_phase                        true
% 3.22/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.01  --inst_lit_sel_side                     num_symb
% 3.22/1.01  --inst_solver_per_active                1400
% 3.22/1.01  --inst_solver_calls_frac                1.
% 3.22/1.01  --inst_passive_queue_type               priority_queues
% 3.22/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.01  --inst_passive_queues_freq              [25;2]
% 3.22/1.01  --inst_dismatching                      true
% 3.22/1.01  --inst_eager_unprocessed_to_passive     true
% 3.22/1.01  --inst_prop_sim_given                   true
% 3.22/1.01  --inst_prop_sim_new                     false
% 3.22/1.01  --inst_subs_new                         false
% 3.22/1.01  --inst_eq_res_simp                      false
% 3.22/1.01  --inst_subs_given                       false
% 3.22/1.01  --inst_orphan_elimination               true
% 3.22/1.01  --inst_learning_loop_flag               true
% 3.22/1.01  --inst_learning_start                   3000
% 3.22/1.01  --inst_learning_factor                  2
% 3.22/1.01  --inst_start_prop_sim_after_learn       3
% 3.22/1.01  --inst_sel_renew                        solver
% 3.22/1.01  --inst_lit_activity_flag                true
% 3.22/1.01  --inst_restr_to_given                   false
% 3.22/1.01  --inst_activity_threshold               500
% 3.22/1.01  --inst_out_proof                        true
% 3.22/1.01  
% 3.22/1.01  ------ Resolution Options
% 3.22/1.01  
% 3.22/1.01  --resolution_flag                       true
% 3.22/1.01  --res_lit_sel                           adaptive
% 3.22/1.01  --res_lit_sel_side                      none
% 3.22/1.01  --res_ordering                          kbo
% 3.22/1.01  --res_to_prop_solver                    active
% 3.22/1.01  --res_prop_simpl_new                    false
% 3.22/1.01  --res_prop_simpl_given                  true
% 3.22/1.01  --res_passive_queue_type                priority_queues
% 3.22/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.01  --res_passive_queues_freq               [15;5]
% 3.22/1.01  --res_forward_subs                      full
% 3.22/1.01  --res_backward_subs                     full
% 3.22/1.01  --res_forward_subs_resolution           true
% 3.22/1.01  --res_backward_subs_resolution          true
% 3.22/1.01  --res_orphan_elimination                true
% 3.22/1.01  --res_time_limit                        2.
% 3.22/1.01  --res_out_proof                         true
% 3.22/1.01  
% 3.22/1.01  ------ Superposition Options
% 3.22/1.01  
% 3.22/1.01  --superposition_flag                    true
% 3.22/1.01  --sup_passive_queue_type                priority_queues
% 3.22/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.01  --demod_completeness_check              fast
% 3.22/1.01  --demod_use_ground                      true
% 3.22/1.01  --sup_to_prop_solver                    passive
% 3.22/1.01  --sup_prop_simpl_new                    true
% 3.22/1.01  --sup_prop_simpl_given                  true
% 3.22/1.01  --sup_fun_splitting                     false
% 3.22/1.01  --sup_smt_interval                      50000
% 3.22/1.01  
% 3.22/1.01  ------ Superposition Simplification Setup
% 3.22/1.01  
% 3.22/1.01  --sup_indices_passive                   []
% 3.22/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.01  --sup_full_bw                           [BwDemod]
% 3.22/1.01  --sup_immed_triv                        [TrivRules]
% 3.22/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.01  --sup_immed_bw_main                     []
% 3.22/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.01  
% 3.22/1.01  ------ Combination Options
% 3.22/1.01  
% 3.22/1.01  --comb_res_mult                         3
% 3.22/1.01  --comb_sup_mult                         2
% 3.22/1.01  --comb_inst_mult                        10
% 3.22/1.01  
% 3.22/1.01  ------ Debug Options
% 3.22/1.01  
% 3.22/1.01  --dbg_backtrace                         false
% 3.22/1.01  --dbg_dump_prop_clauses                 false
% 3.22/1.01  --dbg_dump_prop_clauses_file            -
% 3.22/1.01  --dbg_out_stat                          false
% 3.22/1.01  ------ Parsing...
% 3.22/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/1.01  
% 3.22/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.22/1.01  
% 3.22/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/1.01  
% 3.22/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.01  ------ Proving...
% 3.22/1.01  ------ Problem Properties 
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  clauses                                 24
% 3.22/1.01  conjectures                             5
% 3.22/1.01  EPR                                     1
% 3.22/1.01  Horn                                    20
% 3.22/1.01  unary                                   6
% 3.22/1.01  binary                                  5
% 3.22/1.01  lits                                    64
% 3.22/1.01  lits eq                                 24
% 3.22/1.01  fd_pure                                 0
% 3.22/1.01  fd_pseudo                               0
% 3.22/1.01  fd_cond                                 3
% 3.22/1.01  fd_pseudo_cond                          1
% 3.22/1.01  AC symbols                              0
% 3.22/1.01  
% 3.22/1.01  ------ Schedule dynamic 5 is on 
% 3.22/1.01  
% 3.22/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  ------ 
% 3.22/1.01  Current options:
% 3.22/1.01  ------ 
% 3.22/1.01  
% 3.22/1.01  ------ Input Options
% 3.22/1.01  
% 3.22/1.01  --out_options                           all
% 3.22/1.01  --tptp_safe_out                         true
% 3.22/1.01  --problem_path                          ""
% 3.22/1.01  --include_path                          ""
% 3.22/1.01  --clausifier                            res/vclausify_rel
% 3.22/1.01  --clausifier_options                    --mode clausify
% 3.22/1.01  --stdin                                 false
% 3.22/1.01  --stats_out                             all
% 3.22/1.01  
% 3.22/1.01  ------ General Options
% 3.22/1.01  
% 3.22/1.01  --fof                                   false
% 3.22/1.01  --time_out_real                         305.
% 3.22/1.01  --time_out_virtual                      -1.
% 3.22/1.01  --symbol_type_check                     false
% 3.22/1.01  --clausify_out                          false
% 3.22/1.01  --sig_cnt_out                           false
% 3.22/1.01  --trig_cnt_out                          false
% 3.22/1.01  --trig_cnt_out_tolerance                1.
% 3.22/1.01  --trig_cnt_out_sk_spl                   false
% 3.22/1.01  --abstr_cl_out                          false
% 3.22/1.01  
% 3.22/1.01  ------ Global Options
% 3.22/1.01  
% 3.22/1.01  --schedule                              default
% 3.22/1.01  --add_important_lit                     false
% 3.22/1.01  --prop_solver_per_cl                    1000
% 3.22/1.01  --min_unsat_core                        false
% 3.22/1.01  --soft_assumptions                      false
% 3.22/1.01  --soft_lemma_size                       3
% 3.22/1.01  --prop_impl_unit_size                   0
% 3.22/1.01  --prop_impl_unit                        []
% 3.22/1.01  --share_sel_clauses                     true
% 3.22/1.01  --reset_solvers                         false
% 3.22/1.01  --bc_imp_inh                            [conj_cone]
% 3.22/1.01  --conj_cone_tolerance                   3.
% 3.22/1.01  --extra_neg_conj                        none
% 3.22/1.01  --large_theory_mode                     true
% 3.22/1.01  --prolific_symb_bound                   200
% 3.22/1.01  --lt_threshold                          2000
% 3.22/1.01  --clause_weak_htbl                      true
% 3.22/1.01  --gc_record_bc_elim                     false
% 3.22/1.01  
% 3.22/1.01  ------ Preprocessing Options
% 3.22/1.01  
% 3.22/1.01  --preprocessing_flag                    true
% 3.22/1.01  --time_out_prep_mult                    0.1
% 3.22/1.01  --splitting_mode                        input
% 3.22/1.01  --splitting_grd                         true
% 3.22/1.01  --splitting_cvd                         false
% 3.22/1.01  --splitting_cvd_svl                     false
% 3.22/1.01  --splitting_nvd                         32
% 3.22/1.01  --sub_typing                            true
% 3.22/1.01  --prep_gs_sim                           true
% 3.22/1.01  --prep_unflatten                        true
% 3.22/1.01  --prep_res_sim                          true
% 3.22/1.01  --prep_upred                            true
% 3.22/1.01  --prep_sem_filter                       exhaustive
% 3.22/1.01  --prep_sem_filter_out                   false
% 3.22/1.01  --pred_elim                             true
% 3.22/1.01  --res_sim_input                         true
% 3.22/1.01  --eq_ax_congr_red                       true
% 3.22/1.01  --pure_diseq_elim                       true
% 3.22/1.01  --brand_transform                       false
% 3.22/1.01  --non_eq_to_eq                          false
% 3.22/1.01  --prep_def_merge                        true
% 3.22/1.01  --prep_def_merge_prop_impl              false
% 3.22/1.01  --prep_def_merge_mbd                    true
% 3.22/1.01  --prep_def_merge_tr_red                 false
% 3.22/1.01  --prep_def_merge_tr_cl                  false
% 3.22/1.01  --smt_preprocessing                     true
% 3.22/1.01  --smt_ac_axioms                         fast
% 3.22/1.01  --preprocessed_out                      false
% 3.22/1.01  --preprocessed_stats                    false
% 3.22/1.01  
% 3.22/1.01  ------ Abstraction refinement Options
% 3.22/1.01  
% 3.22/1.01  --abstr_ref                             []
% 3.22/1.01  --abstr_ref_prep                        false
% 3.22/1.01  --abstr_ref_until_sat                   false
% 3.22/1.01  --abstr_ref_sig_restrict                funpre
% 3.22/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.01  --abstr_ref_under                       []
% 3.22/1.01  
% 3.22/1.01  ------ SAT Options
% 3.22/1.01  
% 3.22/1.01  --sat_mode                              false
% 3.22/1.01  --sat_fm_restart_options                ""
% 3.22/1.01  --sat_gr_def                            false
% 3.22/1.01  --sat_epr_types                         true
% 3.22/1.01  --sat_non_cyclic_types                  false
% 3.22/1.01  --sat_finite_models                     false
% 3.22/1.01  --sat_fm_lemmas                         false
% 3.22/1.01  --sat_fm_prep                           false
% 3.22/1.01  --sat_fm_uc_incr                        true
% 3.22/1.01  --sat_out_model                         small
% 3.22/1.01  --sat_out_clauses                       false
% 3.22/1.01  
% 3.22/1.01  ------ QBF Options
% 3.22/1.01  
% 3.22/1.01  --qbf_mode                              false
% 3.22/1.01  --qbf_elim_univ                         false
% 3.22/1.01  --qbf_dom_inst                          none
% 3.22/1.01  --qbf_dom_pre_inst                      false
% 3.22/1.01  --qbf_sk_in                             false
% 3.22/1.01  --qbf_pred_elim                         true
% 3.22/1.01  --qbf_split                             512
% 3.22/1.01  
% 3.22/1.01  ------ BMC1 Options
% 3.22/1.01  
% 3.22/1.01  --bmc1_incremental                      false
% 3.22/1.01  --bmc1_axioms                           reachable_all
% 3.22/1.01  --bmc1_min_bound                        0
% 3.22/1.01  --bmc1_max_bound                        -1
% 3.22/1.01  --bmc1_max_bound_default                -1
% 3.22/1.01  --bmc1_symbol_reachability              true
% 3.22/1.01  --bmc1_property_lemmas                  false
% 3.22/1.01  --bmc1_k_induction                      false
% 3.22/1.01  --bmc1_non_equiv_states                 false
% 3.22/1.01  --bmc1_deadlock                         false
% 3.22/1.01  --bmc1_ucm                              false
% 3.22/1.01  --bmc1_add_unsat_core                   none
% 3.22/1.01  --bmc1_unsat_core_children              false
% 3.22/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.01  --bmc1_out_stat                         full
% 3.22/1.01  --bmc1_ground_init                      false
% 3.22/1.01  --bmc1_pre_inst_next_state              false
% 3.22/1.01  --bmc1_pre_inst_state                   false
% 3.22/1.01  --bmc1_pre_inst_reach_state             false
% 3.22/1.01  --bmc1_out_unsat_core                   false
% 3.22/1.01  --bmc1_aig_witness_out                  false
% 3.22/1.01  --bmc1_verbose                          false
% 3.22/1.01  --bmc1_dump_clauses_tptp                false
% 3.22/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.01  --bmc1_dump_file                        -
% 3.22/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.01  --bmc1_ucm_extend_mode                  1
% 3.22/1.01  --bmc1_ucm_init_mode                    2
% 3.22/1.01  --bmc1_ucm_cone_mode                    none
% 3.22/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.01  --bmc1_ucm_relax_model                  4
% 3.22/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.01  --bmc1_ucm_layered_model                none
% 3.22/1.01  --bmc1_ucm_max_lemma_size               10
% 3.22/1.01  
% 3.22/1.01  ------ AIG Options
% 3.22/1.01  
% 3.22/1.01  --aig_mode                              false
% 3.22/1.01  
% 3.22/1.01  ------ Instantiation Options
% 3.22/1.01  
% 3.22/1.01  --instantiation_flag                    true
% 3.22/1.01  --inst_sos_flag                         false
% 3.22/1.01  --inst_sos_phase                        true
% 3.22/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.01  --inst_lit_sel_side                     none
% 3.22/1.01  --inst_solver_per_active                1400
% 3.22/1.01  --inst_solver_calls_frac                1.
% 3.22/1.01  --inst_passive_queue_type               priority_queues
% 3.22/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.01  --inst_passive_queues_freq              [25;2]
% 3.22/1.01  --inst_dismatching                      true
% 3.22/1.01  --inst_eager_unprocessed_to_passive     true
% 3.22/1.01  --inst_prop_sim_given                   true
% 3.22/1.01  --inst_prop_sim_new                     false
% 3.22/1.01  --inst_subs_new                         false
% 3.22/1.01  --inst_eq_res_simp                      false
% 3.22/1.01  --inst_subs_given                       false
% 3.22/1.01  --inst_orphan_elimination               true
% 3.22/1.01  --inst_learning_loop_flag               true
% 3.22/1.01  --inst_learning_start                   3000
% 3.22/1.01  --inst_learning_factor                  2
% 3.22/1.01  --inst_start_prop_sim_after_learn       3
% 3.22/1.01  --inst_sel_renew                        solver
% 3.22/1.01  --inst_lit_activity_flag                true
% 3.22/1.01  --inst_restr_to_given                   false
% 3.22/1.01  --inst_activity_threshold               500
% 3.22/1.01  --inst_out_proof                        true
% 3.22/1.01  
% 3.22/1.01  ------ Resolution Options
% 3.22/1.01  
% 3.22/1.01  --resolution_flag                       false
% 3.22/1.01  --res_lit_sel                           adaptive
% 3.22/1.01  --res_lit_sel_side                      none
% 3.22/1.01  --res_ordering                          kbo
% 3.22/1.01  --res_to_prop_solver                    active
% 3.22/1.01  --res_prop_simpl_new                    false
% 3.22/1.01  --res_prop_simpl_given                  true
% 3.22/1.01  --res_passive_queue_type                priority_queues
% 3.22/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.01  --res_passive_queues_freq               [15;5]
% 3.22/1.01  --res_forward_subs                      full
% 3.22/1.01  --res_backward_subs                     full
% 3.22/1.01  --res_forward_subs_resolution           true
% 3.22/1.01  --res_backward_subs_resolution          true
% 3.22/1.01  --res_orphan_elimination                true
% 3.22/1.01  --res_time_limit                        2.
% 3.22/1.01  --res_out_proof                         true
% 3.22/1.01  
% 3.22/1.01  ------ Superposition Options
% 3.22/1.01  
% 3.22/1.01  --superposition_flag                    true
% 3.22/1.01  --sup_passive_queue_type                priority_queues
% 3.22/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.01  --demod_completeness_check              fast
% 3.22/1.01  --demod_use_ground                      true
% 3.22/1.01  --sup_to_prop_solver                    passive
% 3.22/1.01  --sup_prop_simpl_new                    true
% 3.22/1.01  --sup_prop_simpl_given                  true
% 3.22/1.01  --sup_fun_splitting                     false
% 3.22/1.01  --sup_smt_interval                      50000
% 3.22/1.01  
% 3.22/1.01  ------ Superposition Simplification Setup
% 3.22/1.01  
% 3.22/1.01  --sup_indices_passive                   []
% 3.22/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.01  --sup_full_bw                           [BwDemod]
% 3.22/1.01  --sup_immed_triv                        [TrivRules]
% 3.22/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.01  --sup_immed_bw_main                     []
% 3.22/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.01  
% 3.22/1.01  ------ Combination Options
% 3.22/1.01  
% 3.22/1.01  --comb_res_mult                         3
% 3.22/1.01  --comb_sup_mult                         2
% 3.22/1.01  --comb_inst_mult                        10
% 3.22/1.01  
% 3.22/1.01  ------ Debug Options
% 3.22/1.01  
% 3.22/1.01  --dbg_backtrace                         false
% 3.22/1.01  --dbg_dump_prop_clauses                 false
% 3.22/1.01  --dbg_dump_prop_clauses_file            -
% 3.22/1.01  --dbg_out_stat                          false
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  ------ Proving...
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  % SZS status Theorem for theBenchmark.p
% 3.22/1.01  
% 3.22/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/1.01  
% 3.22/1.01  fof(f13,conjecture,(
% 3.22/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f14,negated_conjecture,(
% 3.22/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.22/1.01    inference(negated_conjecture,[],[f13])).
% 3.22/1.01  
% 3.22/1.01  fof(f35,plain,(
% 3.22/1.01    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.22/1.01    inference(ennf_transformation,[],[f14])).
% 3.22/1.01  
% 3.22/1.01  fof(f36,plain,(
% 3.22/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.22/1.01    inference(flattening,[],[f35])).
% 3.22/1.01  
% 3.22/1.01  fof(f42,plain,(
% 3.22/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.22/1.01    introduced(choice_axiom,[])).
% 3.22/1.01  
% 3.22/1.01  fof(f41,plain,(
% 3.22/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.22/1.01    introduced(choice_axiom,[])).
% 3.22/1.01  
% 3.22/1.01  fof(f40,plain,(
% 3.22/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.22/1.01    introduced(choice_axiom,[])).
% 3.22/1.01  
% 3.22/1.01  fof(f43,plain,(
% 3.22/1.01    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.22/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).
% 3.22/1.01  
% 3.22/1.01  fof(f72,plain,(
% 3.22/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f9,axiom,(
% 3.22/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f28,plain,(
% 3.22/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.22/1.01    inference(ennf_transformation,[],[f9])).
% 3.22/1.01  
% 3.22/1.01  fof(f61,plain,(
% 3.22/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f28])).
% 3.22/1.01  
% 3.22/1.01  fof(f69,plain,(
% 3.22/1.01    l1_struct_0(sK1)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f67,plain,(
% 3.22/1.01    l1_struct_0(sK0)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f5,axiom,(
% 3.22/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f21,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.01    inference(ennf_transformation,[],[f5])).
% 3.22/1.01  
% 3.22/1.01  fof(f50,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.01    inference(cnf_transformation,[],[f21])).
% 3.22/1.01  
% 3.22/1.01  fof(f73,plain,(
% 3.22/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f6,axiom,(
% 3.22/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f22,plain,(
% 3.22/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.22/1.01    inference(ennf_transformation,[],[f6])).
% 3.22/1.01  
% 3.22/1.01  fof(f23,plain,(
% 3.22/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.22/1.01    inference(flattening,[],[f22])).
% 3.22/1.01  
% 3.22/1.01  fof(f52,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f23])).
% 3.22/1.01  
% 3.22/1.01  fof(f10,axiom,(
% 3.22/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f29,plain,(
% 3.22/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.22/1.01    inference(ennf_transformation,[],[f10])).
% 3.22/1.01  
% 3.22/1.01  fof(f30,plain,(
% 3.22/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.22/1.01    inference(flattening,[],[f29])).
% 3.22/1.01  
% 3.22/1.01  fof(f62,plain,(
% 3.22/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f30])).
% 3.22/1.01  
% 3.22/1.01  fof(f68,plain,(
% 3.22/1.01    ~v2_struct_0(sK1)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f4,axiom,(
% 3.22/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f15,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.22/1.01    inference(pure_predicate_removal,[],[f4])).
% 3.22/1.01  
% 3.22/1.01  fof(f20,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.01    inference(ennf_transformation,[],[f15])).
% 3.22/1.01  
% 3.22/1.01  fof(f49,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.01    inference(cnf_transformation,[],[f20])).
% 3.22/1.01  
% 3.22/1.01  fof(f8,axiom,(
% 3.22/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f26,plain,(
% 3.22/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.22/1.01    inference(ennf_transformation,[],[f8])).
% 3.22/1.01  
% 3.22/1.01  fof(f27,plain,(
% 3.22/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.22/1.01    inference(flattening,[],[f26])).
% 3.22/1.01  
% 3.22/1.01  fof(f39,plain,(
% 3.22/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.22/1.01    inference(nnf_transformation,[],[f27])).
% 3.22/1.01  
% 3.22/1.01  fof(f59,plain,(
% 3.22/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f39])).
% 3.22/1.01  
% 3.22/1.01  fof(f3,axiom,(
% 3.22/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f19,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.01    inference(ennf_transformation,[],[f3])).
% 3.22/1.01  
% 3.22/1.01  fof(f48,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.01    inference(cnf_transformation,[],[f19])).
% 3.22/1.01  
% 3.22/1.01  fof(f70,plain,(
% 3.22/1.01    v1_funct_1(sK2)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f71,plain,(
% 3.22/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f7,axiom,(
% 3.22/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f24,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.01    inference(ennf_transformation,[],[f7])).
% 3.22/1.01  
% 3.22/1.01  fof(f25,plain,(
% 3.22/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.01    inference(flattening,[],[f24])).
% 3.22/1.01  
% 3.22/1.01  fof(f38,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.01    inference(nnf_transformation,[],[f25])).
% 3.22/1.01  
% 3.22/1.01  fof(f53,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.01    inference(cnf_transformation,[],[f38])).
% 3.22/1.01  
% 3.22/1.01  fof(f1,axiom,(
% 3.22/1.01    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f16,plain,(
% 3.22/1.01    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.22/1.01    inference(ennf_transformation,[],[f1])).
% 3.22/1.01  
% 3.22/1.01  fof(f37,plain,(
% 3.22/1.01    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.22/1.01    inference(nnf_transformation,[],[f16])).
% 3.22/1.01  
% 3.22/1.01  fof(f44,plain,(
% 3.22/1.01    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f37])).
% 3.22/1.01  
% 3.22/1.01  fof(f11,axiom,(
% 3.22/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f31,plain,(
% 3.22/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.22/1.01    inference(ennf_transformation,[],[f11])).
% 3.22/1.01  
% 3.22/1.01  fof(f32,plain,(
% 3.22/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.22/1.01    inference(flattening,[],[f31])).
% 3.22/1.01  
% 3.22/1.01  fof(f63,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f32])).
% 3.22/1.01  
% 3.22/1.01  fof(f74,plain,(
% 3.22/1.01    v2_funct_1(sK2)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f75,plain,(
% 3.22/1.01    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 3.22/1.01    inference(cnf_transformation,[],[f43])).
% 3.22/1.01  
% 3.22/1.01  fof(f12,axiom,(
% 3.22/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f33,plain,(
% 3.22/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.22/1.01    inference(ennf_transformation,[],[f12])).
% 3.22/1.01  
% 3.22/1.01  fof(f34,plain,(
% 3.22/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.22/1.01    inference(flattening,[],[f33])).
% 3.22/1.01  
% 3.22/1.01  fof(f65,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f34])).
% 3.22/1.01  
% 3.22/1.01  fof(f66,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f34])).
% 3.22/1.01  
% 3.22/1.01  fof(f2,axiom,(
% 3.22/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.22/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.01  
% 3.22/1.01  fof(f17,plain,(
% 3.22/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/1.01    inference(ennf_transformation,[],[f2])).
% 3.22/1.01  
% 3.22/1.01  fof(f18,plain,(
% 3.22/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/1.01    inference(flattening,[],[f17])).
% 3.22/1.01  
% 3.22/1.01  fof(f47,plain,(
% 3.22/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f18])).
% 3.22/1.01  
% 3.22/1.01  fof(f46,plain,(
% 3.22/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f18])).
% 3.22/1.01  
% 3.22/1.01  fof(f45,plain,(
% 3.22/1.01    ( ! [X0] : (k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.01    inference(cnf_transformation,[],[f37])).
% 3.22/1.01  
% 3.22/1.01  fof(f54,plain,(
% 3.22/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.01    inference(cnf_transformation,[],[f38])).
% 3.22/1.01  
% 3.22/1.01  fof(f80,plain,(
% 3.22/1.01    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.22/1.01    inference(equality_resolution,[],[f54])).
% 3.22/1.01  
% 3.22/1.01  cnf(c_26,negated_conjecture,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.22/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1155,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_17,plain,
% 3.22/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_29,negated_conjecture,
% 3.22/1.01      ( l1_struct_0(sK1) ),
% 3.22/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_349,plain,
% 3.22/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_350,plain,
% 3.22/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_349]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_31,negated_conjecture,
% 3.22/1.01      ( l1_struct_0(sK0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_354,plain,
% 3.22/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_31]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_355,plain,
% 3.22/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_354]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1181,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_1155,c_350,c_355]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_6,plain,
% 3.22/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1165,plain,
% 3.22/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.22/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1605,plain,
% 3.22/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1181,c_1165]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_25,negated_conjecture,
% 3.22/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.22/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1178,plain,
% 3.22/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_25,c_350,c_355]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1869,plain,
% 3.22/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1605,c_1178]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1876,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1869,c_1181]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_7,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | v1_partfun1(X0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | v1_xboole_0(X2)
% 3.22/1.01      | ~ v1_funct_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_18,plain,
% 3.22/1.01      ( v2_struct_0(X0)
% 3.22/1.01      | ~ l1_struct_0(X0)
% 3.22/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.22/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_30,negated_conjecture,
% 3.22/1.01      ( ~ v2_struct_0(sK1) ),
% 3.22/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_336,plain,
% 3.22/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_337,plain,
% 3.22/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_336]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_339,plain,
% 3.22/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_337,c_29]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_361,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | v1_partfun1(X0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ v1_funct_1(X0)
% 3.22/1.01      | u1_struct_0(sK1) != X2 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_339]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_362,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.22/1.01      | v1_partfun1(X0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.22/1.01      | ~ v1_funct_1(X0) ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_5,plain,
% 3.22/1.01      ( v4_relat_1(X0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.22/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_16,plain,
% 3.22/1.01      ( ~ v1_partfun1(X0,X1)
% 3.22/1.01      | ~ v4_relat_1(X0,X1)
% 3.22/1.01      | ~ v1_relat_1(X0)
% 3.22/1.01      | k1_relat_1(X0) = X1 ),
% 3.22/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_384,plain,
% 3.22/1.01      ( ~ v1_partfun1(X0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ v1_relat_1(X0)
% 3.22/1.01      | k1_relat_1(X0) = X1 ),
% 3.22/1.01      inference(resolution,[status(thm)],[c_5,c_16]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4,plain,
% 3.22/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | v1_relat_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_388,plain,
% 3.22/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ v1_partfun1(X0,X1)
% 3.22/1.01      | k1_relat_1(X0) = X1 ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_384,c_16,c_5,c_4]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_389,plain,
% 3.22/1.01      ( ~ v1_partfun1(X0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | k1_relat_1(X0) = X1 ),
% 3.22/1.01      inference(renaming,[status(thm)],[c_388]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_428,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.22/1.01      | ~ v1_funct_1(X0)
% 3.22/1.01      | k1_relat_1(X0) = X1 ),
% 3.22/1.01      inference(resolution,[status(thm)],[c_362,c_389]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1152,plain,
% 3.22/1.01      ( k1_relat_1(X0) = X1
% 3.22/1.01      | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
% 3.22/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
% 3.22/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1291,plain,
% 3.22/1.01      ( k1_relat_1(X0) = X1
% 3.22/1.01      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 3.22/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 3.22/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_1152,c_350]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1784,plain,
% 3.22/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.22/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.22/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1181,c_1291]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_28,negated_conjecture,
% 3.22/1.01      ( v1_funct_1(sK2) ),
% 3.22/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_35,plain,
% 3.22/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_27,negated_conjecture,
% 3.22/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.22/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1154,plain,
% 3.22/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1175,plain,
% 3.22/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_1154,c_350,c_355]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2798,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 3.22/1.01      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_1784,c_35,c_1175]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2799,plain,
% 3.22/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.22/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
% 3.22/1.01      inference(renaming,[status(thm)],[c_2798]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2806,plain,
% 3.22/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1876,c_2799]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_14,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.22/1.01      | k1_xboole_0 = X2 ),
% 3.22/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1159,plain,
% 3.22/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 3.22/1.01      | k1_xboole_0 = X1
% 3.22/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.22/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2866,plain,
% 3.22/1.01      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 3.22/1.01      | k2_relat_1(sK2) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1876,c_1159]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1877,plain,
% 3.22/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1869,c_1175]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3259,plain,
% 3.22/1.01      ( k2_relat_1(sK2) = k1_xboole_0
% 3.22/1.01      | k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_2866,c_1877]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3260,plain,
% 3.22/1.01      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 3.22/1.01      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.22/1.01      inference(renaming,[status(thm)],[c_3259]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3395,plain,
% 3.22/1.01      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 3.22/1.01      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_2806,c_3260]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1359,plain,
% 3.22/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.22/1.01      | v1_relat_1(sK2) ),
% 3.22/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1,plain,
% 3.22/1.01      ( ~ v1_relat_1(X0)
% 3.22/1.01      | k2_relat_1(X0) = k1_xboole_0
% 3.22/1.01      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.22/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1410,plain,
% 3.22/1.01      ( ~ v1_relat_1(sK2)
% 3.22/1.01      | k2_relat_1(sK2) = k1_xboole_0
% 3.22/1.01      | k1_relat_1(sK2) != k1_xboole_0 ),
% 3.22/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_19,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ v1_funct_1(X0)
% 3.22/1.01      | ~ v2_funct_1(X0)
% 3.22/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.22/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.22/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_24,negated_conjecture,
% 3.22/1.01      ( v2_funct_1(sK2) ),
% 3.22/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_456,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ v1_funct_1(X0)
% 3.22/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.22/1.01      | k2_relset_1(X1,X2,X0) != X2
% 3.22/1.01      | sK2 != X0 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_457,plain,
% 3.22/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 3.22/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.01      | ~ v1_funct_1(sK2)
% 3.22/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.22/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_456]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_461,plain,
% 3.22/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 3.22/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.22/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_457,c_28]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_462,plain,
% 3.22/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 3.22/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.22/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.22/1.01      inference(renaming,[status(thm)],[c_461]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1151,plain,
% 3.22/1.01      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.22/1.01      | k2_relset_1(X0,X1,sK2) != X1
% 3.22/1.01      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.22/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1611,plain,
% 3.22/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.22/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.22/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1178,c_1151]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1731,plain,
% 3.22/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_1611,c_1181,c_1175]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_23,negated_conjecture,
% 3.22/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.22/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1254,plain,
% 3.22/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.22/1.01      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_23,c_350,c_355]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1734,plain,
% 3.22/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 3.22/1.01      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1731,c_1254]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1874,plain,
% 3.22/1.01      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.22/1.01      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1869,c_1734]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3396,plain,
% 3.22/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.22/1.01      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_2806,c_1874]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3397,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_2806,c_1876]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3400,plain,
% 3.22/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_2806,c_1877]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1875,plain,
% 3.22/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1869,c_1731]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3398,plain,
% 3.22/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_2806,c_1875]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_21,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | ~ v1_funct_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1157,plain,
% 3.22/1.01      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.22/1.01      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 3.22/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3622,plain,
% 3.22/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.22/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.22/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_3398,c_1157]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_20,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.01      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.22/1.01      | ~ v1_funct_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1158,plain,
% 3.22/1.01      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.22/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.01      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 3.22/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3064,plain,
% 3.22/1.01      ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
% 3.22/1.01      | v1_funct_2(X2,X1,X0) != iProver_top
% 3.22/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.22/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1158,c_1165]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3937,plain,
% 3.22/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
% 3.22/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_3397,c_3064]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2,plain,
% 3.22/1.01      ( ~ v1_funct_1(X0)
% 3.22/1.01      | ~ v2_funct_1(X0)
% 3.22/1.01      | ~ v1_relat_1(X0)
% 3.22/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_494,plain,
% 3.22/1.01      ( ~ v1_funct_1(X0)
% 3.22/1.01      | ~ v1_relat_1(X0)
% 3.22/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.22/1.01      | sK2 != X0 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_495,plain,
% 3.22/1.01      ( ~ v1_funct_1(sK2)
% 3.22/1.01      | ~ v1_relat_1(sK2)
% 3.22/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_494]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_497,plain,
% 3.22/1.01      ( ~ v1_relat_1(sK2)
% 3.22/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_495,c_28]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1149,plain,
% 3.22/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.22/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1406,plain,
% 3.22/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_1149,c_28,c_26,c_495,c_1359]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3941,plain,
% 3.22/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.22/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_3937,c_1406,c_3398]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3059,plain,
% 3.22/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.22/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.22/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1875,c_1158]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4151,plain,
% 3.22/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_3059,c_35,c_1876,c_1877]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4155,plain,
% 3.22/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_4151,c_2806]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4161,plain,
% 3.22/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.22/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_4155,c_1159]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4290,plain,
% 3.22/1.01      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_3395,c_35,c_26,c_1359,c_1410,c_3396,c_3397,c_3400,
% 3.22/1.01                 c_3622,c_3941,c_4161]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4298,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_4290,c_3397]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3,plain,
% 3.22/1.01      ( ~ v1_funct_1(X0)
% 3.22/1.01      | ~ v2_funct_1(X0)
% 3.22/1.01      | ~ v1_relat_1(X0)
% 3.22/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.22/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_480,plain,
% 3.22/1.01      ( ~ v1_funct_1(X0)
% 3.22/1.01      | ~ v1_relat_1(X0)
% 3.22/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.22/1.01      | sK2 != X0 ),
% 3.22/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_481,plain,
% 3.22/1.01      ( ~ v1_funct_1(sK2)
% 3.22/1.01      | ~ v1_relat_1(sK2)
% 3.22/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.22/1.01      inference(unflattening,[status(thm)],[c_480]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_483,plain,
% 3.22/1.01      ( ~ v1_relat_1(sK2)
% 3.22/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_481,c_28]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1150,plain,
% 3.22/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.22/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1459,plain,
% 3.22/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_1150,c_28,c_26,c_481,c_1359]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1167,plain,
% 3.22/1.01      ( k2_relat_1(X0) = k1_xboole_0
% 3.22/1.01      | k1_relat_1(X0) != k1_xboole_0
% 3.22/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1548,plain,
% 3.22/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.22/1.01      | k2_relat_1(sK2) != k1_xboole_0
% 3.22/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1459,c_1167]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1549,plain,
% 3.22/1.01      ( k2_relat_1(sK2) != k1_xboole_0
% 3.22/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 3.22/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_1548,c_1406]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_0,plain,
% 3.22/1.01      ( ~ v1_relat_1(X0)
% 3.22/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.22/1.01      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.22/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1411,plain,
% 3.22/1.01      ( ~ v1_relat_1(sK2)
% 3.22/1.01      | k2_relat_1(sK2) != k1_xboole_0
% 3.22/1.01      | k1_relat_1(sK2) = k1_xboole_0 ),
% 3.22/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2553,plain,
% 3.22/1.01      ( k1_relat_1(sK2) = k1_xboole_0 | k2_relat_1(sK2) != k1_xboole_0 ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_1549,c_26,c_1359,c_1411]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_2554,plain,
% 3.22/1.01      ( k2_relat_1(sK2) != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 3.22/1.01      inference(renaming,[status(thm)],[c_2553]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4303,plain,
% 3.22/1.01      ( k1_relat_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_4290,c_2554]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4313,plain,
% 3.22/1.01      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.22/1.01      inference(equality_resolution_simp,[status(thm)],[c_4303]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4335,plain,
% 3.22/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_4298,c_4313]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_13,plain,
% 3.22/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.22/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.22/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.22/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_1160,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.22/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.22/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_3065,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 3.22/1.01      | v1_funct_2(k2_tops_2(X0,k1_xboole_0,X1),k1_xboole_0,X0) != iProver_top
% 3.22/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 3.22/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_1158,c_1160]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_5293,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,X0,k2_tops_2(X0,k1_xboole_0,X1)) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 3.22/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 3.22/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.22/1.01      inference(forward_subsumption_resolution,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_3065,c_1157]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_6764,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,sK2)) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(superposition,[status(thm)],[c_4335,c_5293]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4300,plain,
% 3.22/1.01      ( k2_tops_2(k1_relat_1(sK2),k1_xboole_0,sK2) = k2_funct_1(sK2) ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_4290,c_3398]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4329,plain,
% 3.22/1.01      ( k2_tops_2(k1_xboole_0,k1_xboole_0,sK2) = k2_funct_1(sK2) ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_4300,c_4313]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_6790,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
% 3.22/1.01      | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.22/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_6764,c_4329]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4237,plain,
% 3.22/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 3.22/1.01      inference(global_propositional_subsumption,
% 3.22/1.01                [status(thm)],
% 3.22/1.01                [c_3396,c_35,c_3400,c_3941]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4294,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK2),k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_4290,c_4237]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4347,plain,
% 3.22/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_4294,c_4313]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4301,plain,
% 3.22/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 3.22/1.01      inference(demodulation,[status(thm)],[c_4290,c_3400]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(c_4326,plain,
% 3.22/1.01      ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.22/1.01      inference(light_normalisation,[status(thm)],[c_4301,c_4313]) ).
% 3.22/1.01  
% 3.22/1.01  cnf(contradiction,plain,
% 3.22/1.01      ( $false ),
% 3.22/1.01      inference(minisat,[status(thm)],[c_6790,c_4347,c_4326,c_35]) ).
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/1.01  
% 3.22/1.01  ------                               Statistics
% 3.22/1.01  
% 3.22/1.01  ------ General
% 3.22/1.01  
% 3.22/1.01  abstr_ref_over_cycles:                  0
% 3.22/1.01  abstr_ref_under_cycles:                 0
% 3.22/1.01  gc_basic_clause_elim:                   0
% 3.22/1.01  forced_gc_time:                         0
% 3.22/1.01  parsing_time:                           0.011
% 3.22/1.01  unif_index_cands_time:                  0.
% 3.22/1.01  unif_index_add_time:                    0.
% 3.22/1.01  orderings_time:                         0.
% 3.22/1.01  out_proof_time:                         0.011
% 3.22/1.01  total_time:                             0.236
% 3.22/1.01  num_of_symbols:                         55
% 3.22/1.01  num_of_terms:                           6676
% 3.22/1.01  
% 3.22/1.01  ------ Preprocessing
% 3.22/1.01  
% 3.22/1.01  num_of_splits:                          0
% 3.22/1.01  num_of_split_atoms:                     0
% 3.22/1.01  num_of_reused_defs:                     0
% 3.22/1.01  num_eq_ax_congr_red:                    4
% 3.22/1.01  num_of_sem_filtered_clauses:            1
% 3.22/1.01  num_of_subtypes:                        0
% 3.22/1.01  monotx_restored_types:                  0
% 3.22/1.01  sat_num_of_epr_types:                   0
% 3.22/1.01  sat_num_of_non_cyclic_types:            0
% 3.22/1.01  sat_guarded_non_collapsed_types:        0
% 3.22/1.01  num_pure_diseq_elim:                    0
% 3.22/1.01  simp_replaced_by:                       0
% 3.22/1.01  res_preprocessed:                       136
% 3.22/1.01  prep_upred:                             0
% 3.22/1.01  prep_unflattend:                        15
% 3.22/1.01  smt_new_axioms:                         0
% 3.22/1.01  pred_elim_cands:                        4
% 3.22/1.01  pred_elim:                              6
% 3.22/1.01  pred_elim_cl:                           7
% 3.22/1.01  pred_elim_cycles:                       8
% 3.22/1.01  merged_defs:                            0
% 3.22/1.01  merged_defs_ncl:                        0
% 3.22/1.01  bin_hyper_res:                          0
% 3.22/1.01  prep_cycles:                            4
% 3.22/1.01  pred_elim_time:                         0.005
% 3.22/1.01  splitting_time:                         0.
% 3.22/1.01  sem_filter_time:                        0.
% 3.22/1.01  monotx_time:                            0.
% 3.22/1.01  subtype_inf_time:                       0.
% 3.22/1.01  
% 3.22/1.01  ------ Problem properties
% 3.22/1.01  
% 3.22/1.01  clauses:                                24
% 3.22/1.01  conjectures:                            5
% 3.22/1.01  epr:                                    1
% 3.22/1.01  horn:                                   20
% 3.22/1.01  ground:                                 9
% 3.22/1.01  unary:                                  6
% 3.22/1.01  binary:                                 5
% 3.22/1.01  lits:                                   64
% 3.22/1.01  lits_eq:                                24
% 3.22/1.01  fd_pure:                                0
% 3.22/1.01  fd_pseudo:                              0
% 3.22/1.01  fd_cond:                                3
% 3.22/1.01  fd_pseudo_cond:                         1
% 3.22/1.01  ac_symbols:                             0
% 3.22/1.01  
% 3.22/1.01  ------ Propositional Solver
% 3.22/1.01  
% 3.22/1.01  prop_solver_calls:                      30
% 3.22/1.01  prop_fast_solver_calls:                 1085
% 3.22/1.01  smt_solver_calls:                       0
% 3.22/1.01  smt_fast_solver_calls:                  0
% 3.22/1.01  prop_num_of_clauses:                    2486
% 3.22/1.01  prop_preprocess_simplified:             6774
% 3.22/1.01  prop_fo_subsumed:                       39
% 3.22/1.01  prop_solver_time:                       0.
% 3.22/1.01  smt_solver_time:                        0.
% 3.22/1.01  smt_fast_solver_time:                   0.
% 3.22/1.01  prop_fast_solver_time:                  0.
% 3.22/1.01  prop_unsat_core_time:                   0.
% 3.22/1.01  
% 3.22/1.01  ------ QBF
% 3.22/1.01  
% 3.22/1.01  qbf_q_res:                              0
% 3.22/1.01  qbf_num_tautologies:                    0
% 3.22/1.01  qbf_prep_cycles:                        0
% 3.22/1.01  
% 3.22/1.01  ------ BMC1
% 3.22/1.01  
% 3.22/1.01  bmc1_current_bound:                     -1
% 3.22/1.01  bmc1_last_solved_bound:                 -1
% 3.22/1.01  bmc1_unsat_core_size:                   -1
% 3.22/1.01  bmc1_unsat_core_parents_size:           -1
% 3.22/1.01  bmc1_merge_next_fun:                    0
% 3.22/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.22/1.01  
% 3.22/1.01  ------ Instantiation
% 3.22/1.01  
% 3.22/1.01  inst_num_of_clauses:                    991
% 3.22/1.01  inst_num_in_passive:                    374
% 3.22/1.01  inst_num_in_active:                     337
% 3.22/1.01  inst_num_in_unprocessed:                280
% 3.22/1.01  inst_num_of_loops:                      400
% 3.22/1.01  inst_num_of_learning_restarts:          0
% 3.22/1.01  inst_num_moves_active_passive:          59
% 3.22/1.01  inst_lit_activity:                      0
% 3.22/1.01  inst_lit_activity_moves:                0
% 3.22/1.01  inst_num_tautologies:                   0
% 3.22/1.01  inst_num_prop_implied:                  0
% 3.22/1.01  inst_num_existing_simplified:           0
% 3.22/1.01  inst_num_eq_res_simplified:             0
% 3.22/1.01  inst_num_child_elim:                    0
% 3.22/1.01  inst_num_of_dismatching_blockings:      96
% 3.22/1.01  inst_num_of_non_proper_insts:           565
% 3.22/1.01  inst_num_of_duplicates:                 0
% 3.22/1.01  inst_inst_num_from_inst_to_res:         0
% 3.22/1.01  inst_dismatching_checking_time:         0.
% 3.22/1.01  
% 3.22/1.01  ------ Resolution
% 3.22/1.01  
% 3.22/1.01  res_num_of_clauses:                     0
% 3.22/1.01  res_num_in_passive:                     0
% 3.22/1.01  res_num_in_active:                      0
% 3.22/1.01  res_num_of_loops:                       140
% 3.22/1.01  res_forward_subset_subsumed:            51
% 3.22/1.01  res_backward_subset_subsumed:           2
% 3.22/1.01  res_forward_subsumed:                   0
% 3.22/1.01  res_backward_subsumed:                  0
% 3.22/1.01  res_forward_subsumption_resolution:     1
% 3.22/1.01  res_backward_subsumption_resolution:    0
% 3.22/1.01  res_clause_to_clause_subsumption:       204
% 3.22/1.01  res_orphan_elimination:                 0
% 3.22/1.01  res_tautology_del:                      71
% 3.22/1.01  res_num_eq_res_simplified:              0
% 3.22/1.01  res_num_sel_changes:                    0
% 3.22/1.01  res_moves_from_active_to_pass:          0
% 3.22/1.01  
% 3.22/1.01  ------ Superposition
% 3.22/1.01  
% 3.22/1.01  sup_time_total:                         0.
% 3.22/1.01  sup_time_generating:                    0.
% 3.22/1.01  sup_time_sim_full:                      0.
% 3.22/1.01  sup_time_sim_immed:                     0.
% 3.22/1.01  
% 3.22/1.01  sup_num_of_clauses:                     57
% 3.22/1.01  sup_num_in_active:                      43
% 3.22/1.01  sup_num_in_passive:                     14
% 3.22/1.01  sup_num_of_loops:                       78
% 3.22/1.01  sup_fw_superposition:                   24
% 3.22/1.01  sup_bw_superposition:                   50
% 3.22/1.01  sup_immediate_simplified:               41
% 3.22/1.01  sup_given_eliminated:                   0
% 3.22/1.01  comparisons_done:                       0
% 3.22/1.01  comparisons_avoided:                    4
% 3.22/1.01  
% 3.22/1.01  ------ Simplifications
% 3.22/1.01  
% 3.22/1.01  
% 3.22/1.01  sim_fw_subset_subsumed:                 15
% 3.22/1.01  sim_bw_subset_subsumed:                 5
% 3.22/1.01  sim_fw_subsumed:                        3
% 3.22/1.01  sim_bw_subsumed:                        0
% 3.22/1.01  sim_fw_subsumption_res:                 8
% 3.22/1.01  sim_bw_subsumption_res:                 0
% 3.22/1.01  sim_tautology_del:                      0
% 3.22/1.01  sim_eq_tautology_del:                   9
% 3.22/1.01  sim_eq_res_simp:                        1
% 3.22/1.01  sim_fw_demodulated:                     3
% 3.22/1.01  sim_bw_demodulated:                     34
% 3.22/1.01  sim_light_normalised:                   30
% 3.22/1.01  sim_joinable_taut:                      0
% 3.22/1.01  sim_joinable_simp:                      0
% 3.22/1.01  sim_ac_normalised:                      0
% 3.22/1.01  sim_smt_subsumption:                    0
% 3.22/1.01  
%------------------------------------------------------------------------------
