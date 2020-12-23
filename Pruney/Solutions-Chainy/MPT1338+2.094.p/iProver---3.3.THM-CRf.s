%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:19 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  144 (1780 expanded)
%              Number of clauses        :   89 ( 489 expanded)
%              Number of leaves         :   15 ( 540 expanded)
%              Depth                    :   19
%              Number of atoms          :  472 (13059 expanded)
%              Number of equality atoms :  208 (4520 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32,f31])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_926,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_320,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_321,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_325,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_326,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_951,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_926,c_321,c_326])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1320,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_936])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1216,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1217,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_2723,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_33,c_1193,c_1217])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_442,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_443,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_445,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_24])).

cnf(c_920,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_2729,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2723,c_920])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_948,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_21,c_321,c_326])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_404,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_405,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_24])).

cnf(c_410,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_922,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_1594,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_922])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_925,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_945,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_925,c_321,c_326])).

cnf(c_1597,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1594,c_945,c_951])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_933,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1604,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1597,c_933])).

cnf(c_1245,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_951,c_933])).

cnf(c_1738,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1245,c_948])).

cnf(c_2720,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1604,c_1738])).

cnf(c_3023,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2729,c_2720])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_927,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1747,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_927])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_293,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_311,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_293,c_26])).

cnf(c_312,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_3178,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1747,c_25,c_312,c_945])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_934,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1249,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_951,c_934])).

cnf(c_2450,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1249,c_1738])).

cnf(c_3180,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3178,c_1738,c_2450])).

cnf(c_3847,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3023,c_3180])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_332,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_333,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_337,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_24])).

cnf(c_338,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_924,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_1424,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_924])).

cnf(c_1486,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1424,c_945,c_951])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1018,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_19,c_321,c_326])).

cnf(c_1489,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1486,c_1018])).

cnf(c_2153,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1738,c_1489])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_428,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_429,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_431,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_24])).

cnf(c_921,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_2728,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2723,c_921])).

cnf(c_1603,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1597,c_934])).

cnf(c_2550,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1603,c_1738])).

cnf(c_2918,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2728,c_2550])).

cnf(c_3118,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_2918])).

cnf(c_3182,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3180,c_3118])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3847,c_3182])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:38:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.19/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/0.94  
% 2.19/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.94  
% 2.19/0.94  ------  iProver source info
% 2.19/0.94  
% 2.19/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.94  git: non_committed_changes: false
% 2.19/0.94  git: last_make_outside_of_git: false
% 2.19/0.94  
% 2.19/0.94  ------ 
% 2.19/0.94  
% 2.19/0.94  ------ Input Options
% 2.19/0.94  
% 2.19/0.94  --out_options                           all
% 2.19/0.94  --tptp_safe_out                         true
% 2.19/0.94  --problem_path                          ""
% 2.19/0.94  --include_path                          ""
% 2.19/0.94  --clausifier                            res/vclausify_rel
% 2.19/0.94  --clausifier_options                    --mode clausify
% 2.19/0.94  --stdin                                 false
% 2.19/0.94  --stats_out                             all
% 2.19/0.94  
% 2.19/0.94  ------ General Options
% 2.19/0.94  
% 2.19/0.94  --fof                                   false
% 2.19/0.94  --time_out_real                         305.
% 2.19/0.94  --time_out_virtual                      -1.
% 2.19/0.94  --symbol_type_check                     false
% 2.19/0.94  --clausify_out                          false
% 2.19/0.94  --sig_cnt_out                           false
% 2.19/0.94  --trig_cnt_out                          false
% 2.19/0.94  --trig_cnt_out_tolerance                1.
% 2.19/0.94  --trig_cnt_out_sk_spl                   false
% 2.19/0.94  --abstr_cl_out                          false
% 2.19/0.94  
% 2.19/0.94  ------ Global Options
% 2.19/0.94  
% 2.19/0.94  --schedule                              default
% 2.19/0.94  --add_important_lit                     false
% 2.19/0.94  --prop_solver_per_cl                    1000
% 2.19/0.94  --min_unsat_core                        false
% 2.19/0.94  --soft_assumptions                      false
% 2.19/0.94  --soft_lemma_size                       3
% 2.19/0.94  --prop_impl_unit_size                   0
% 2.19/0.94  --prop_impl_unit                        []
% 2.19/0.94  --share_sel_clauses                     true
% 2.19/0.94  --reset_solvers                         false
% 2.19/0.94  --bc_imp_inh                            [conj_cone]
% 2.19/0.94  --conj_cone_tolerance                   3.
% 2.19/0.94  --extra_neg_conj                        none
% 2.19/0.94  --large_theory_mode                     true
% 2.19/0.94  --prolific_symb_bound                   200
% 2.19/0.94  --lt_threshold                          2000
% 2.19/0.94  --clause_weak_htbl                      true
% 2.19/0.94  --gc_record_bc_elim                     false
% 2.19/0.95  
% 2.19/0.95  ------ Preprocessing Options
% 2.19/0.95  
% 2.19/0.95  --preprocessing_flag                    true
% 2.19/0.95  --time_out_prep_mult                    0.1
% 2.19/0.95  --splitting_mode                        input
% 2.19/0.95  --splitting_grd                         true
% 2.19/0.95  --splitting_cvd                         false
% 2.19/0.95  --splitting_cvd_svl                     false
% 2.19/0.95  --splitting_nvd                         32
% 2.19/0.95  --sub_typing                            true
% 2.19/0.95  --prep_gs_sim                           true
% 2.19/0.95  --prep_unflatten                        true
% 2.19/0.95  --prep_res_sim                          true
% 2.19/0.95  --prep_upred                            true
% 2.19/0.95  --prep_sem_filter                       exhaustive
% 2.19/0.95  --prep_sem_filter_out                   false
% 2.19/0.95  --pred_elim                             true
% 2.19/0.95  --res_sim_input                         true
% 2.19/0.95  --eq_ax_congr_red                       true
% 2.19/0.95  --pure_diseq_elim                       true
% 2.19/0.95  --brand_transform                       false
% 2.19/0.95  --non_eq_to_eq                          false
% 2.19/0.95  --prep_def_merge                        true
% 2.19/0.95  --prep_def_merge_prop_impl              false
% 2.19/0.95  --prep_def_merge_mbd                    true
% 2.19/0.95  --prep_def_merge_tr_red                 false
% 2.19/0.95  --prep_def_merge_tr_cl                  false
% 2.19/0.95  --smt_preprocessing                     true
% 2.19/0.95  --smt_ac_axioms                         fast
% 2.19/0.95  --preprocessed_out                      false
% 2.19/0.95  --preprocessed_stats                    false
% 2.19/0.95  
% 2.19/0.95  ------ Abstraction refinement Options
% 2.19/0.95  
% 2.19/0.95  --abstr_ref                             []
% 2.19/0.95  --abstr_ref_prep                        false
% 2.19/0.95  --abstr_ref_until_sat                   false
% 2.19/0.95  --abstr_ref_sig_restrict                funpre
% 2.19/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.95  --abstr_ref_under                       []
% 2.19/0.95  
% 2.19/0.95  ------ SAT Options
% 2.19/0.95  
% 2.19/0.95  --sat_mode                              false
% 2.19/0.95  --sat_fm_restart_options                ""
% 2.19/0.95  --sat_gr_def                            false
% 2.19/0.95  --sat_epr_types                         true
% 2.19/0.95  --sat_non_cyclic_types                  false
% 2.19/0.95  --sat_finite_models                     false
% 2.19/0.95  --sat_fm_lemmas                         false
% 2.19/0.95  --sat_fm_prep                           false
% 2.19/0.95  --sat_fm_uc_incr                        true
% 2.19/0.95  --sat_out_model                         small
% 2.19/0.95  --sat_out_clauses                       false
% 2.19/0.95  
% 2.19/0.95  ------ QBF Options
% 2.19/0.95  
% 2.19/0.95  --qbf_mode                              false
% 2.19/0.95  --qbf_elim_univ                         false
% 2.19/0.95  --qbf_dom_inst                          none
% 2.19/0.95  --qbf_dom_pre_inst                      false
% 2.19/0.95  --qbf_sk_in                             false
% 2.19/0.95  --qbf_pred_elim                         true
% 2.19/0.95  --qbf_split                             512
% 2.19/0.95  
% 2.19/0.95  ------ BMC1 Options
% 2.19/0.95  
% 2.19/0.95  --bmc1_incremental                      false
% 2.19/0.95  --bmc1_axioms                           reachable_all
% 2.19/0.95  --bmc1_min_bound                        0
% 2.19/0.95  --bmc1_max_bound                        -1
% 2.19/0.95  --bmc1_max_bound_default                -1
% 2.19/0.95  --bmc1_symbol_reachability              true
% 2.19/0.95  --bmc1_property_lemmas                  false
% 2.19/0.95  --bmc1_k_induction                      false
% 2.19/0.95  --bmc1_non_equiv_states                 false
% 2.19/0.95  --bmc1_deadlock                         false
% 2.19/0.95  --bmc1_ucm                              false
% 2.19/0.95  --bmc1_add_unsat_core                   none
% 2.19/0.95  --bmc1_unsat_core_children              false
% 2.19/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.95  --bmc1_out_stat                         full
% 2.19/0.95  --bmc1_ground_init                      false
% 2.19/0.95  --bmc1_pre_inst_next_state              false
% 2.19/0.95  --bmc1_pre_inst_state                   false
% 2.19/0.95  --bmc1_pre_inst_reach_state             false
% 2.19/0.95  --bmc1_out_unsat_core                   false
% 2.19/0.95  --bmc1_aig_witness_out                  false
% 2.19/0.95  --bmc1_verbose                          false
% 2.19/0.95  --bmc1_dump_clauses_tptp                false
% 2.19/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.95  --bmc1_dump_file                        -
% 2.19/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.95  --bmc1_ucm_extend_mode                  1
% 2.19/0.95  --bmc1_ucm_init_mode                    2
% 2.19/0.95  --bmc1_ucm_cone_mode                    none
% 2.19/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.95  --bmc1_ucm_relax_model                  4
% 2.19/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.95  --bmc1_ucm_layered_model                none
% 2.19/0.95  --bmc1_ucm_max_lemma_size               10
% 2.19/0.95  
% 2.19/0.95  ------ AIG Options
% 2.19/0.95  
% 2.19/0.95  --aig_mode                              false
% 2.19/0.95  
% 2.19/0.95  ------ Instantiation Options
% 2.19/0.95  
% 2.19/0.95  --instantiation_flag                    true
% 2.19/0.95  --inst_sos_flag                         false
% 2.19/0.95  --inst_sos_phase                        true
% 2.19/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.95  --inst_lit_sel_side                     num_symb
% 2.19/0.95  --inst_solver_per_active                1400
% 2.19/0.95  --inst_solver_calls_frac                1.
% 2.19/0.95  --inst_passive_queue_type               priority_queues
% 2.19/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.95  --inst_passive_queues_freq              [25;2]
% 2.19/0.95  --inst_dismatching                      true
% 2.19/0.95  --inst_eager_unprocessed_to_passive     true
% 2.19/0.95  --inst_prop_sim_given                   true
% 2.19/0.95  --inst_prop_sim_new                     false
% 2.19/0.95  --inst_subs_new                         false
% 2.19/0.95  --inst_eq_res_simp                      false
% 2.19/0.95  --inst_subs_given                       false
% 2.19/0.95  --inst_orphan_elimination               true
% 2.19/0.95  --inst_learning_loop_flag               true
% 2.19/0.95  --inst_learning_start                   3000
% 2.19/0.95  --inst_learning_factor                  2
% 2.19/0.95  --inst_start_prop_sim_after_learn       3
% 2.19/0.95  --inst_sel_renew                        solver
% 2.19/0.95  --inst_lit_activity_flag                true
% 2.19/0.95  --inst_restr_to_given                   false
% 2.19/0.95  --inst_activity_threshold               500
% 2.19/0.95  --inst_out_proof                        true
% 2.19/0.95  
% 2.19/0.95  ------ Resolution Options
% 2.19/0.95  
% 2.19/0.95  --resolution_flag                       true
% 2.19/0.95  --res_lit_sel                           adaptive
% 2.19/0.95  --res_lit_sel_side                      none
% 2.19/0.95  --res_ordering                          kbo
% 2.19/0.95  --res_to_prop_solver                    active
% 2.19/0.95  --res_prop_simpl_new                    false
% 2.19/0.95  --res_prop_simpl_given                  true
% 2.19/0.95  --res_passive_queue_type                priority_queues
% 2.19/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.95  --res_passive_queues_freq               [15;5]
% 2.19/0.95  --res_forward_subs                      full
% 2.19/0.95  --res_backward_subs                     full
% 2.19/0.95  --res_forward_subs_resolution           true
% 2.19/0.95  --res_backward_subs_resolution          true
% 2.19/0.95  --res_orphan_elimination                true
% 2.19/0.95  --res_time_limit                        2.
% 2.19/0.95  --res_out_proof                         true
% 2.19/0.95  
% 2.19/0.95  ------ Superposition Options
% 2.19/0.95  
% 2.19/0.95  --superposition_flag                    true
% 2.19/0.95  --sup_passive_queue_type                priority_queues
% 2.19/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.95  --demod_completeness_check              fast
% 2.19/0.95  --demod_use_ground                      true
% 2.19/0.95  --sup_to_prop_solver                    passive
% 2.19/0.95  --sup_prop_simpl_new                    true
% 2.19/0.95  --sup_prop_simpl_given                  true
% 2.19/0.95  --sup_fun_splitting                     false
% 2.19/0.95  --sup_smt_interval                      50000
% 2.19/0.95  
% 2.19/0.95  ------ Superposition Simplification Setup
% 2.19/0.95  
% 2.19/0.95  --sup_indices_passive                   []
% 2.19/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.95  --sup_full_bw                           [BwDemod]
% 2.19/0.95  --sup_immed_triv                        [TrivRules]
% 2.19/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.95  --sup_immed_bw_main                     []
% 2.19/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.95  
% 2.19/0.95  ------ Combination Options
% 2.19/0.95  
% 2.19/0.95  --comb_res_mult                         3
% 2.19/0.95  --comb_sup_mult                         2
% 2.19/0.95  --comb_inst_mult                        10
% 2.19/0.95  
% 2.19/0.95  ------ Debug Options
% 2.19/0.95  
% 2.19/0.95  --dbg_backtrace                         false
% 2.19/0.95  --dbg_dump_prop_clauses                 false
% 2.19/0.95  --dbg_dump_prop_clauses_file            -
% 2.19/0.95  --dbg_out_stat                          false
% 2.19/0.95  ------ Parsing...
% 2.19/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.95  
% 2.19/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.19/0.95  
% 2.19/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.95  
% 2.19/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.95  ------ Proving...
% 2.19/0.95  ------ Problem Properties 
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  clauses                                 22
% 2.19/0.95  conjectures                             4
% 2.19/0.95  EPR                                     0
% 2.19/0.95  Horn                                    18
% 2.19/0.95  unary                                   7
% 2.19/0.95  binary                                  5
% 2.19/0.95  lits                                    53
% 2.19/0.95  lits eq                                 23
% 2.19/0.95  fd_pure                                 0
% 2.19/0.95  fd_pseudo                               0
% 2.19/0.95  fd_cond                                 3
% 2.19/0.95  fd_pseudo_cond                          0
% 2.19/0.95  AC symbols                              0
% 2.19/0.95  
% 2.19/0.95  ------ Schedule dynamic 5 is on 
% 2.19/0.95  
% 2.19/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  ------ 
% 2.19/0.95  Current options:
% 2.19/0.95  ------ 
% 2.19/0.95  
% 2.19/0.95  ------ Input Options
% 2.19/0.95  
% 2.19/0.95  --out_options                           all
% 2.19/0.95  --tptp_safe_out                         true
% 2.19/0.95  --problem_path                          ""
% 2.19/0.95  --include_path                          ""
% 2.19/0.95  --clausifier                            res/vclausify_rel
% 2.19/0.95  --clausifier_options                    --mode clausify
% 2.19/0.95  --stdin                                 false
% 2.19/0.95  --stats_out                             all
% 2.19/0.95  
% 2.19/0.95  ------ General Options
% 2.19/0.95  
% 2.19/0.95  --fof                                   false
% 2.19/0.95  --time_out_real                         305.
% 2.19/0.95  --time_out_virtual                      -1.
% 2.19/0.95  --symbol_type_check                     false
% 2.19/0.95  --clausify_out                          false
% 2.19/0.95  --sig_cnt_out                           false
% 2.19/0.95  --trig_cnt_out                          false
% 2.19/0.95  --trig_cnt_out_tolerance                1.
% 2.19/0.95  --trig_cnt_out_sk_spl                   false
% 2.19/0.95  --abstr_cl_out                          false
% 2.19/0.95  
% 2.19/0.95  ------ Global Options
% 2.19/0.95  
% 2.19/0.95  --schedule                              default
% 2.19/0.95  --add_important_lit                     false
% 2.19/0.95  --prop_solver_per_cl                    1000
% 2.19/0.95  --min_unsat_core                        false
% 2.19/0.95  --soft_assumptions                      false
% 2.19/0.95  --soft_lemma_size                       3
% 2.19/0.95  --prop_impl_unit_size                   0
% 2.19/0.95  --prop_impl_unit                        []
% 2.19/0.95  --share_sel_clauses                     true
% 2.19/0.95  --reset_solvers                         false
% 2.19/0.95  --bc_imp_inh                            [conj_cone]
% 2.19/0.95  --conj_cone_tolerance                   3.
% 2.19/0.95  --extra_neg_conj                        none
% 2.19/0.95  --large_theory_mode                     true
% 2.19/0.95  --prolific_symb_bound                   200
% 2.19/0.95  --lt_threshold                          2000
% 2.19/0.95  --clause_weak_htbl                      true
% 2.19/0.95  --gc_record_bc_elim                     false
% 2.19/0.95  
% 2.19/0.95  ------ Preprocessing Options
% 2.19/0.95  
% 2.19/0.95  --preprocessing_flag                    true
% 2.19/0.95  --time_out_prep_mult                    0.1
% 2.19/0.95  --splitting_mode                        input
% 2.19/0.95  --splitting_grd                         true
% 2.19/0.95  --splitting_cvd                         false
% 2.19/0.95  --splitting_cvd_svl                     false
% 2.19/0.95  --splitting_nvd                         32
% 2.19/0.95  --sub_typing                            true
% 2.19/0.95  --prep_gs_sim                           true
% 2.19/0.95  --prep_unflatten                        true
% 2.19/0.95  --prep_res_sim                          true
% 2.19/0.95  --prep_upred                            true
% 2.19/0.95  --prep_sem_filter                       exhaustive
% 2.19/0.95  --prep_sem_filter_out                   false
% 2.19/0.95  --pred_elim                             true
% 2.19/0.95  --res_sim_input                         true
% 2.19/0.95  --eq_ax_congr_red                       true
% 2.19/0.95  --pure_diseq_elim                       true
% 2.19/0.95  --brand_transform                       false
% 2.19/0.95  --non_eq_to_eq                          false
% 2.19/0.95  --prep_def_merge                        true
% 2.19/0.95  --prep_def_merge_prop_impl              false
% 2.19/0.95  --prep_def_merge_mbd                    true
% 2.19/0.95  --prep_def_merge_tr_red                 false
% 2.19/0.95  --prep_def_merge_tr_cl                  false
% 2.19/0.95  --smt_preprocessing                     true
% 2.19/0.95  --smt_ac_axioms                         fast
% 2.19/0.95  --preprocessed_out                      false
% 2.19/0.95  --preprocessed_stats                    false
% 2.19/0.95  
% 2.19/0.95  ------ Abstraction refinement Options
% 2.19/0.95  
% 2.19/0.95  --abstr_ref                             []
% 2.19/0.95  --abstr_ref_prep                        false
% 2.19/0.95  --abstr_ref_until_sat                   false
% 2.19/0.95  --abstr_ref_sig_restrict                funpre
% 2.19/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.95  --abstr_ref_under                       []
% 2.19/0.95  
% 2.19/0.95  ------ SAT Options
% 2.19/0.95  
% 2.19/0.95  --sat_mode                              false
% 2.19/0.95  --sat_fm_restart_options                ""
% 2.19/0.95  --sat_gr_def                            false
% 2.19/0.95  --sat_epr_types                         true
% 2.19/0.95  --sat_non_cyclic_types                  false
% 2.19/0.95  --sat_finite_models                     false
% 2.19/0.95  --sat_fm_lemmas                         false
% 2.19/0.95  --sat_fm_prep                           false
% 2.19/0.95  --sat_fm_uc_incr                        true
% 2.19/0.95  --sat_out_model                         small
% 2.19/0.95  --sat_out_clauses                       false
% 2.19/0.95  
% 2.19/0.95  ------ QBF Options
% 2.19/0.95  
% 2.19/0.95  --qbf_mode                              false
% 2.19/0.95  --qbf_elim_univ                         false
% 2.19/0.95  --qbf_dom_inst                          none
% 2.19/0.95  --qbf_dom_pre_inst                      false
% 2.19/0.95  --qbf_sk_in                             false
% 2.19/0.95  --qbf_pred_elim                         true
% 2.19/0.95  --qbf_split                             512
% 2.19/0.95  
% 2.19/0.95  ------ BMC1 Options
% 2.19/0.95  
% 2.19/0.95  --bmc1_incremental                      false
% 2.19/0.95  --bmc1_axioms                           reachable_all
% 2.19/0.95  --bmc1_min_bound                        0
% 2.19/0.95  --bmc1_max_bound                        -1
% 2.19/0.95  --bmc1_max_bound_default                -1
% 2.19/0.95  --bmc1_symbol_reachability              true
% 2.19/0.95  --bmc1_property_lemmas                  false
% 2.19/0.95  --bmc1_k_induction                      false
% 2.19/0.95  --bmc1_non_equiv_states                 false
% 2.19/0.95  --bmc1_deadlock                         false
% 2.19/0.95  --bmc1_ucm                              false
% 2.19/0.95  --bmc1_add_unsat_core                   none
% 2.19/0.95  --bmc1_unsat_core_children              false
% 2.19/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.95  --bmc1_out_stat                         full
% 2.19/0.95  --bmc1_ground_init                      false
% 2.19/0.95  --bmc1_pre_inst_next_state              false
% 2.19/0.95  --bmc1_pre_inst_state                   false
% 2.19/0.95  --bmc1_pre_inst_reach_state             false
% 2.19/0.95  --bmc1_out_unsat_core                   false
% 2.19/0.95  --bmc1_aig_witness_out                  false
% 2.19/0.95  --bmc1_verbose                          false
% 2.19/0.95  --bmc1_dump_clauses_tptp                false
% 2.19/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.95  --bmc1_dump_file                        -
% 2.19/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.95  --bmc1_ucm_extend_mode                  1
% 2.19/0.95  --bmc1_ucm_init_mode                    2
% 2.19/0.95  --bmc1_ucm_cone_mode                    none
% 2.19/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.95  --bmc1_ucm_relax_model                  4
% 2.19/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.95  --bmc1_ucm_layered_model                none
% 2.19/0.95  --bmc1_ucm_max_lemma_size               10
% 2.19/0.95  
% 2.19/0.95  ------ AIG Options
% 2.19/0.95  
% 2.19/0.95  --aig_mode                              false
% 2.19/0.95  
% 2.19/0.95  ------ Instantiation Options
% 2.19/0.95  
% 2.19/0.95  --instantiation_flag                    true
% 2.19/0.95  --inst_sos_flag                         false
% 2.19/0.95  --inst_sos_phase                        true
% 2.19/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.95  --inst_lit_sel_side                     none
% 2.19/0.95  --inst_solver_per_active                1400
% 2.19/0.95  --inst_solver_calls_frac                1.
% 2.19/0.95  --inst_passive_queue_type               priority_queues
% 2.19/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.95  --inst_passive_queues_freq              [25;2]
% 2.19/0.95  --inst_dismatching                      true
% 2.19/0.95  --inst_eager_unprocessed_to_passive     true
% 2.19/0.95  --inst_prop_sim_given                   true
% 2.19/0.95  --inst_prop_sim_new                     false
% 2.19/0.95  --inst_subs_new                         false
% 2.19/0.95  --inst_eq_res_simp                      false
% 2.19/0.95  --inst_subs_given                       false
% 2.19/0.95  --inst_orphan_elimination               true
% 2.19/0.95  --inst_learning_loop_flag               true
% 2.19/0.95  --inst_learning_start                   3000
% 2.19/0.95  --inst_learning_factor                  2
% 2.19/0.95  --inst_start_prop_sim_after_learn       3
% 2.19/0.95  --inst_sel_renew                        solver
% 2.19/0.95  --inst_lit_activity_flag                true
% 2.19/0.95  --inst_restr_to_given                   false
% 2.19/0.95  --inst_activity_threshold               500
% 2.19/0.95  --inst_out_proof                        true
% 2.19/0.95  
% 2.19/0.95  ------ Resolution Options
% 2.19/0.95  
% 2.19/0.95  --resolution_flag                       false
% 2.19/0.95  --res_lit_sel                           adaptive
% 2.19/0.95  --res_lit_sel_side                      none
% 2.19/0.95  --res_ordering                          kbo
% 2.19/0.95  --res_to_prop_solver                    active
% 2.19/0.95  --res_prop_simpl_new                    false
% 2.19/0.95  --res_prop_simpl_given                  true
% 2.19/0.95  --res_passive_queue_type                priority_queues
% 2.19/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.95  --res_passive_queues_freq               [15;5]
% 2.19/0.95  --res_forward_subs                      full
% 2.19/0.95  --res_backward_subs                     full
% 2.19/0.95  --res_forward_subs_resolution           true
% 2.19/0.95  --res_backward_subs_resolution          true
% 2.19/0.95  --res_orphan_elimination                true
% 2.19/0.95  --res_time_limit                        2.
% 2.19/0.95  --res_out_proof                         true
% 2.19/0.95  
% 2.19/0.95  ------ Superposition Options
% 2.19/0.95  
% 2.19/0.95  --superposition_flag                    true
% 2.19/0.95  --sup_passive_queue_type                priority_queues
% 2.19/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.95  --demod_completeness_check              fast
% 2.19/0.95  --demod_use_ground                      true
% 2.19/0.95  --sup_to_prop_solver                    passive
% 2.19/0.95  --sup_prop_simpl_new                    true
% 2.19/0.95  --sup_prop_simpl_given                  true
% 2.19/0.95  --sup_fun_splitting                     false
% 2.19/0.95  --sup_smt_interval                      50000
% 2.19/0.95  
% 2.19/0.95  ------ Superposition Simplification Setup
% 2.19/0.95  
% 2.19/0.95  --sup_indices_passive                   []
% 2.19/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.95  --sup_full_bw                           [BwDemod]
% 2.19/0.95  --sup_immed_triv                        [TrivRules]
% 2.19/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.95  --sup_immed_bw_main                     []
% 2.19/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.95  
% 2.19/0.95  ------ Combination Options
% 2.19/0.95  
% 2.19/0.95  --comb_res_mult                         3
% 2.19/0.95  --comb_sup_mult                         2
% 2.19/0.95  --comb_inst_mult                        10
% 2.19/0.95  
% 2.19/0.95  ------ Debug Options
% 2.19/0.95  
% 2.19/0.95  --dbg_backtrace                         false
% 2.19/0.95  --dbg_dump_prop_clauses                 false
% 2.19/0.95  --dbg_dump_prop_clauses_file            -
% 2.19/0.95  --dbg_out_stat                          false
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  ------ Proving...
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  % SZS status Theorem for theBenchmark.p
% 2.19/0.95  
% 2.19/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.95  
% 2.19/0.95  fof(f12,conjecture,(
% 2.19/0.95    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f13,negated_conjecture,(
% 2.19/0.95    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.19/0.95    inference(negated_conjecture,[],[f12])).
% 2.19/0.95  
% 2.19/0.95  fof(f28,plain,(
% 2.19/0.95    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.19/0.95    inference(ennf_transformation,[],[f13])).
% 2.19/0.95  
% 2.19/0.95  fof(f29,plain,(
% 2.19/0.95    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.19/0.95    inference(flattening,[],[f28])).
% 2.19/0.95  
% 2.19/0.95  fof(f33,plain,(
% 2.19/0.95    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.19/0.95    introduced(choice_axiom,[])).
% 2.19/0.95  
% 2.19/0.95  fof(f32,plain,(
% 2.19/0.95    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.19/0.95    introduced(choice_axiom,[])).
% 2.19/0.95  
% 2.19/0.95  fof(f31,plain,(
% 2.19/0.95    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.19/0.95    introduced(choice_axiom,[])).
% 2.19/0.95  
% 2.19/0.95  fof(f34,plain,(
% 2.19/0.95    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32,f31])).
% 2.19/0.95  
% 2.19/0.95  fof(f59,plain,(
% 2.19/0.95    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f9,axiom,(
% 2.19/0.95    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f23,plain,(
% 2.19/0.95    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.19/0.95    inference(ennf_transformation,[],[f9])).
% 2.19/0.95  
% 2.19/0.95  fof(f51,plain,(
% 2.19/0.95    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f23])).
% 2.19/0.95  
% 2.19/0.95  fof(f56,plain,(
% 2.19/0.95    l1_struct_0(sK1)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f54,plain,(
% 2.19/0.95    l1_struct_0(sK0)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f2,axiom,(
% 2.19/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f14,plain,(
% 2.19/0.95    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.19/0.95    inference(ennf_transformation,[],[f2])).
% 2.19/0.95  
% 2.19/0.95  fof(f36,plain,(
% 2.19/0.95    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f14])).
% 2.19/0.95  
% 2.19/0.95  fof(f3,axiom,(
% 2.19/0.95    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f37,plain,(
% 2.19/0.95    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.19/0.95    inference(cnf_transformation,[],[f3])).
% 2.19/0.95  
% 2.19/0.95  fof(f4,axiom,(
% 2.19/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f15,plain,(
% 2.19/0.95    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.95    inference(ennf_transformation,[],[f4])).
% 2.19/0.95  
% 2.19/0.95  fof(f16,plain,(
% 2.19/0.95    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.95    inference(flattening,[],[f15])).
% 2.19/0.95  
% 2.19/0.95  fof(f39,plain,(
% 2.19/0.95    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f16])).
% 2.19/0.95  
% 2.19/0.95  fof(f61,plain,(
% 2.19/0.95    v2_funct_1(sK2)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f57,plain,(
% 2.19/0.95    v1_funct_1(sK2)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f60,plain,(
% 2.19/0.95    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f8,axiom,(
% 2.19/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f21,plain,(
% 2.19/0.95    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.95    inference(ennf_transformation,[],[f8])).
% 2.19/0.95  
% 2.19/0.95  fof(f22,plain,(
% 2.19/0.95    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.95    inference(flattening,[],[f21])).
% 2.19/0.95  
% 2.19/0.95  fof(f50,plain,(
% 2.19/0.95    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f22])).
% 2.19/0.95  
% 2.19/0.95  fof(f58,plain,(
% 2.19/0.95    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f6,axiom,(
% 2.19/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f18,plain,(
% 2.19/0.95    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.95    inference(ennf_transformation,[],[f6])).
% 2.19/0.95  
% 2.19/0.95  fof(f41,plain,(
% 2.19/0.95    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.95    inference(cnf_transformation,[],[f18])).
% 2.19/0.95  
% 2.19/0.95  fof(f7,axiom,(
% 2.19/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f19,plain,(
% 2.19/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.95    inference(ennf_transformation,[],[f7])).
% 2.19/0.95  
% 2.19/0.95  fof(f20,plain,(
% 2.19/0.95    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.95    inference(flattening,[],[f19])).
% 2.19/0.95  
% 2.19/0.95  fof(f30,plain,(
% 2.19/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.95    inference(nnf_transformation,[],[f20])).
% 2.19/0.95  
% 2.19/0.95  fof(f42,plain,(
% 2.19/0.95    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.95    inference(cnf_transformation,[],[f30])).
% 2.19/0.95  
% 2.19/0.95  fof(f1,axiom,(
% 2.19/0.95    v1_xboole_0(k1_xboole_0)),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f35,plain,(
% 2.19/0.95    v1_xboole_0(k1_xboole_0)),
% 2.19/0.95    inference(cnf_transformation,[],[f1])).
% 2.19/0.95  
% 2.19/0.95  fof(f10,axiom,(
% 2.19/0.95    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f24,plain,(
% 2.19/0.95    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.19/0.95    inference(ennf_transformation,[],[f10])).
% 2.19/0.95  
% 2.19/0.95  fof(f25,plain,(
% 2.19/0.95    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.19/0.95    inference(flattening,[],[f24])).
% 2.19/0.95  
% 2.19/0.95  fof(f52,plain,(
% 2.19/0.95    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f25])).
% 2.19/0.95  
% 2.19/0.95  fof(f55,plain,(
% 2.19/0.95    ~v2_struct_0(sK1)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f5,axiom,(
% 2.19/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f17,plain,(
% 2.19/0.95    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.95    inference(ennf_transformation,[],[f5])).
% 2.19/0.95  
% 2.19/0.95  fof(f40,plain,(
% 2.19/0.95    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.95    inference(cnf_transformation,[],[f17])).
% 2.19/0.95  
% 2.19/0.95  fof(f11,axiom,(
% 2.19/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.95  
% 2.19/0.95  fof(f26,plain,(
% 2.19/0.95    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.95    inference(ennf_transformation,[],[f11])).
% 2.19/0.95  
% 2.19/0.95  fof(f27,plain,(
% 2.19/0.95    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.95    inference(flattening,[],[f26])).
% 2.19/0.95  
% 2.19/0.95  fof(f53,plain,(
% 2.19/0.95    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f27])).
% 2.19/0.95  
% 2.19/0.95  fof(f62,plain,(
% 2.19/0.95    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.19/0.95    inference(cnf_transformation,[],[f34])).
% 2.19/0.95  
% 2.19/0.95  fof(f38,plain,(
% 2.19/0.95    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.95    inference(cnf_transformation,[],[f16])).
% 2.19/0.95  
% 2.19/0.95  cnf(c_22,negated_conjecture,
% 2.19/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.19/0.95      inference(cnf_transformation,[],[f59]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_926,plain,
% 2.19/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_16,plain,
% 2.19/0.95      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f51]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_25,negated_conjecture,
% 2.19/0.95      ( l1_struct_0(sK1) ),
% 2.19/0.95      inference(cnf_transformation,[],[f56]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_320,plain,
% 2.19/0.95      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_321,plain,
% 2.19/0.95      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_320]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_27,negated_conjecture,
% 2.19/0.95      ( l1_struct_0(sK0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f54]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_325,plain,
% 2.19/0.95      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_326,plain,
% 2.19/0.95      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_325]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_951,plain,
% 2.19/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_926,c_321,c_326]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1,plain,
% 2.19/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.19/0.95      | ~ v1_relat_1(X1)
% 2.19/0.95      | v1_relat_1(X0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f36]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_936,plain,
% 2.19/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.19/0.95      | v1_relat_1(X1) != iProver_top
% 2.19/0.95      | v1_relat_1(X0) = iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1320,plain,
% 2.19/0.95      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.19/0.95      | v1_relat_1(sK2) = iProver_top ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_951,c_936]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_33,plain,
% 2.19/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1095,plain,
% 2.19/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | v1_relat_1(X0)
% 2.19/0.95      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.19/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1192,plain,
% 2.19/0.95      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.19/0.95      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.19/0.95      | v1_relat_1(sK2) ),
% 2.19/0.95      inference(instantiation,[status(thm)],[c_1095]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1193,plain,
% 2.19/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.95      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.19/0.95      | v1_relat_1(sK2) = iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2,plain,
% 2.19/0.95      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/0.95      inference(cnf_transformation,[],[f37]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1216,plain,
% 2.19/0.95      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.19/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1217,plain,
% 2.19/0.95      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2723,plain,
% 2.19/0.95      ( v1_relat_1(sK2) = iProver_top ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_1320,c_33,c_1193,c_1217]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3,plain,
% 2.19/0.95      ( ~ v1_funct_1(X0)
% 2.19/0.95      | ~ v2_funct_1(X0)
% 2.19/0.95      | ~ v1_relat_1(X0)
% 2.19/0.95      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_20,negated_conjecture,
% 2.19/0.95      ( v2_funct_1(sK2) ),
% 2.19/0.95      inference(cnf_transformation,[],[f61]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_442,plain,
% 2.19/0.95      ( ~ v1_funct_1(X0)
% 2.19/0.95      | ~ v1_relat_1(X0)
% 2.19/0.95      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.19/0.95      | sK2 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_443,plain,
% 2.19/0.95      ( ~ v1_funct_1(sK2)
% 2.19/0.95      | ~ v1_relat_1(sK2)
% 2.19/0.95      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_442]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_24,negated_conjecture,
% 2.19/0.95      ( v1_funct_1(sK2) ),
% 2.19/0.95      inference(cnf_transformation,[],[f57]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_445,plain,
% 2.19/0.95      ( ~ v1_relat_1(sK2)
% 2.19/0.95      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_443,c_24]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_920,plain,
% 2.19/0.95      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.19/0.95      | v1_relat_1(sK2) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2729,plain,
% 2.19/0.95      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_2723,c_920]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_21,negated_conjecture,
% 2.19/0.95      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/0.95      inference(cnf_transformation,[],[f60]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_948,plain,
% 2.19/0.95      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_21,c_321,c_326]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_13,plain,
% 2.19/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.19/0.95      | ~ v1_funct_1(X0)
% 2.19/0.95      | ~ v2_funct_1(X0)
% 2.19/0.95      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/0.95      inference(cnf_transformation,[],[f50]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_404,plain,
% 2.19/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.19/0.95      | ~ v1_funct_1(X0)
% 2.19/0.95      | k2_relset_1(X1,X2,X0) != X2
% 2.19/0.95      | sK2 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_405,plain,
% 2.19/0.95      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.19/0.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.95      | ~ v1_funct_1(sK2)
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_404]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_409,plain,
% 2.19/0.95      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.19/0.95      | ~ v1_funct_2(sK2,X0,X1)
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_405,c_24]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_410,plain,
% 2.19/0.95      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.19/0.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/0.95      inference(renaming,[status(thm)],[c_409]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_922,plain,
% 2.19/0.95      ( k2_relset_1(X0,X1,sK2) != X1
% 2.19/0.95      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.19/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.19/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1594,plain,
% 2.19/0.95      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.95      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.19/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_948,c_922]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_23,negated_conjecture,
% 2.19/0.95      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.19/0.95      inference(cnf_transformation,[],[f58]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_925,plain,
% 2.19/0.95      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_945,plain,
% 2.19/0.95      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_925,c_321,c_326]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1597,plain,
% 2.19/0.95      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_1594,c_945,c_951]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_6,plain,
% 2.19/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_933,plain,
% 2.19/0.95      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.19/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1604,plain,
% 2.19/0.95      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_1597,c_933]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1245,plain,
% 2.19/0.95      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_951,c_933]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1738,plain,
% 2.19/0.95      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.19/0.95      inference(demodulation,[status(thm)],[c_1245,c_948]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2720,plain,
% 2.19/0.95      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_1604,c_1738]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3023,plain,
% 2.19/0.95      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(demodulation,[status(thm)],[c_2729,c_2720]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_12,plain,
% 2.19/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | k1_relset_1(X1,X2,X0) = X1
% 2.19/0.95      | k1_xboole_0 = X2 ),
% 2.19/0.95      inference(cnf_transformation,[],[f42]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_927,plain,
% 2.19/0.95      ( k1_relset_1(X0,X1,X2) = X0
% 2.19/0.95      | k1_xboole_0 = X1
% 2.19/0.95      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.19/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1747,plain,
% 2.19/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
% 2.19/0.95      | k2_struct_0(sK1) = k1_xboole_0
% 2.19/0.95      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_951,c_927]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_0,plain,
% 2.19/0.95      ( v1_xboole_0(k1_xboole_0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f35]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_17,plain,
% 2.19/0.95      ( v2_struct_0(X0)
% 2.19/0.95      | ~ l1_struct_0(X0)
% 2.19/0.95      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.19/0.95      inference(cnf_transformation,[],[f52]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_293,plain,
% 2.19/0.95      ( v2_struct_0(X0)
% 2.19/0.95      | ~ l1_struct_0(X0)
% 2.19/0.95      | k2_struct_0(X0) != k1_xboole_0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_26,negated_conjecture,
% 2.19/0.95      ( ~ v2_struct_0(sK1) ),
% 2.19/0.95      inference(cnf_transformation,[],[f55]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_311,plain,
% 2.19/0.95      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_293,c_26]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_312,plain,
% 2.19/0.95      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_311]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3178,plain,
% 2.19/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_1747,c_25,c_312,c_945]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_5,plain,
% 2.19/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_934,plain,
% 2.19/0.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.19/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1249,plain,
% 2.19/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_951,c_934]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2450,plain,
% 2.19/0.95      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_1249,c_1738]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3180,plain,
% 2.19/0.95      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_3178,c_1738,c_2450]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3847,plain,
% 2.19/0.95      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_3023,c_3180]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_18,plain,
% 2.19/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | ~ v1_funct_1(X0)
% 2.19/0.95      | ~ v2_funct_1(X0)
% 2.19/0.95      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.19/0.95      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/0.95      inference(cnf_transformation,[],[f53]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_332,plain,
% 2.19/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.95      | ~ v1_funct_1(X0)
% 2.19/0.95      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.19/0.95      | k2_relset_1(X1,X2,X0) != X2
% 2.19/0.95      | sK2 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_333,plain,
% 2.19/0.95      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/0.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.95      | ~ v1_funct_1(sK2)
% 2.19/0.95      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_332]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_337,plain,
% 2.19/0.95      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.95      | ~ v1_funct_2(sK2,X0,X1)
% 2.19/0.95      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_333,c_24]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_338,plain,
% 2.19/0.95      ( ~ v1_funct_2(sK2,X0,X1)
% 2.19/0.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.95      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.19/0.95      inference(renaming,[status(thm)],[c_337]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_924,plain,
% 2.19/0.95      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.19/0.95      | k2_relset_1(X0,X1,sK2) != X1
% 2.19/0.95      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.19/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1424,plain,
% 2.19/0.95      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.19/0.95      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.95      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_948,c_924]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1486,plain,
% 2.19/0.95      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_1424,c_945,c_951]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_19,negated_conjecture,
% 2.19/0.95      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.19/0.95      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.19/0.95      inference(cnf_transformation,[],[f62]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1018,plain,
% 2.19/0.95      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.19/0.95      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_19,c_321,c_326]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1489,plain,
% 2.19/0.95      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.19/0.95      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.19/0.95      inference(demodulation,[status(thm)],[c_1486,c_1018]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2153,plain,
% 2.19/0.95      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.19/0.95      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.19/0.95      inference(demodulation,[status(thm)],[c_1738,c_1489]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_4,plain,
% 2.19/0.95      ( ~ v1_funct_1(X0)
% 2.19/0.95      | ~ v2_funct_1(X0)
% 2.19/0.95      | ~ v1_relat_1(X0)
% 2.19/0.95      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.19/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_428,plain,
% 2.19/0.95      ( ~ v1_funct_1(X0)
% 2.19/0.95      | ~ v1_relat_1(X0)
% 2.19/0.95      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.19/0.95      | sK2 != X0 ),
% 2.19/0.95      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_429,plain,
% 2.19/0.95      ( ~ v1_funct_1(sK2)
% 2.19/0.95      | ~ v1_relat_1(sK2)
% 2.19/0.95      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/0.95      inference(unflattening,[status(thm)],[c_428]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_431,plain,
% 2.19/0.95      ( ~ v1_relat_1(sK2)
% 2.19/0.95      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_429,c_24]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_921,plain,
% 2.19/0.95      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.19/0.95      | v1_relat_1(sK2) != iProver_top ),
% 2.19/0.95      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2728,plain,
% 2.19/0.95      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_2723,c_921]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_1603,plain,
% 2.19/0.95      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.19/0.95      inference(superposition,[status(thm)],[c_1597,c_934]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2550,plain,
% 2.19/0.95      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.19/0.95      inference(light_normalisation,[status(thm)],[c_1603,c_1738]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_2918,plain,
% 2.19/0.95      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.19/0.95      inference(demodulation,[status(thm)],[c_2728,c_2550]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3118,plain,
% 2.19/0.95      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.19/0.95      inference(global_propositional_subsumption,
% 2.19/0.95                [status(thm)],
% 2.19/0.95                [c_2153,c_2918]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(c_3182,plain,
% 2.19/0.95      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.19/0.95      inference(demodulation,[status(thm)],[c_3180,c_3118]) ).
% 2.19/0.95  
% 2.19/0.95  cnf(contradiction,plain,
% 2.19/0.95      ( $false ),
% 2.19/0.95      inference(minisat,[status(thm)],[c_3847,c_3182]) ).
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.95  
% 2.19/0.95  ------                               Statistics
% 2.19/0.95  
% 2.19/0.95  ------ General
% 2.19/0.95  
% 2.19/0.95  abstr_ref_over_cycles:                  0
% 2.19/0.95  abstr_ref_under_cycles:                 0
% 2.19/0.95  gc_basic_clause_elim:                   0
% 2.19/0.95  forced_gc_time:                         0
% 2.19/0.95  parsing_time:                           0.008
% 2.19/0.95  unif_index_cands_time:                  0.
% 2.19/0.95  unif_index_add_time:                    0.
% 2.19/0.95  orderings_time:                         0.
% 2.19/0.95  out_proof_time:                         0.007
% 2.19/0.95  total_time:                             0.143
% 2.19/0.95  num_of_symbols:                         53
% 2.19/0.95  num_of_terms:                           3729
% 2.19/0.95  
% 2.19/0.95  ------ Preprocessing
% 2.19/0.95  
% 2.19/0.95  num_of_splits:                          0
% 2.19/0.95  num_of_split_atoms:                     0
% 2.19/0.95  num_of_reused_defs:                     0
% 2.19/0.95  num_eq_ax_congr_red:                    1
% 2.19/0.95  num_of_sem_filtered_clauses:            1
% 2.19/0.95  num_of_subtypes:                        0
% 2.19/0.95  monotx_restored_types:                  0
% 2.19/0.95  sat_num_of_epr_types:                   0
% 2.19/0.95  sat_num_of_non_cyclic_types:            0
% 2.19/0.95  sat_guarded_non_collapsed_types:        0
% 2.19/0.95  num_pure_diseq_elim:                    0
% 2.19/0.95  simp_replaced_by:                       0
% 2.19/0.95  res_preprocessed:                       125
% 2.19/0.95  prep_upred:                             0
% 2.19/0.95  prep_unflattend:                        9
% 2.19/0.95  smt_new_axioms:                         0
% 2.19/0.95  pred_elim_cands:                        3
% 2.19/0.95  pred_elim:                              5
% 2.19/0.95  pred_elim_cl:                           6
% 2.19/0.95  pred_elim_cycles:                       7
% 2.19/0.95  merged_defs:                            0
% 2.19/0.95  merged_defs_ncl:                        0
% 2.19/0.95  bin_hyper_res:                          0
% 2.19/0.95  prep_cycles:                            4
% 2.19/0.95  pred_elim_time:                         0.005
% 2.19/0.95  splitting_time:                         0.
% 2.19/0.95  sem_filter_time:                        0.
% 2.19/0.95  monotx_time:                            0.001
% 2.19/0.95  subtype_inf_time:                       0.
% 2.19/0.95  
% 2.19/0.95  ------ Problem properties
% 2.19/0.95  
% 2.19/0.95  clauses:                                22
% 2.19/0.95  conjectures:                            4
% 2.19/0.95  epr:                                    0
% 2.19/0.95  horn:                                   18
% 2.19/0.95  ground:                                 9
% 2.19/0.95  unary:                                  7
% 2.19/0.95  binary:                                 5
% 2.19/0.95  lits:                                   53
% 2.19/0.95  lits_eq:                                23
% 2.19/0.95  fd_pure:                                0
% 2.19/0.95  fd_pseudo:                              0
% 2.19/0.95  fd_cond:                                3
% 2.19/0.95  fd_pseudo_cond:                         0
% 2.19/0.95  ac_symbols:                             0
% 2.19/0.95  
% 2.19/0.95  ------ Propositional Solver
% 2.19/0.95  
% 2.19/0.95  prop_solver_calls:                      29
% 2.19/0.95  prop_fast_solver_calls:                 815
% 2.19/0.95  smt_solver_calls:                       0
% 2.19/0.95  smt_fast_solver_calls:                  0
% 2.19/0.95  prop_num_of_clauses:                    1252
% 2.19/0.95  prop_preprocess_simplified:             4248
% 2.19/0.95  prop_fo_subsumed:                       19
% 2.19/0.95  prop_solver_time:                       0.
% 2.19/0.95  smt_solver_time:                        0.
% 2.19/0.95  smt_fast_solver_time:                   0.
% 2.19/0.95  prop_fast_solver_time:                  0.
% 2.19/0.95  prop_unsat_core_time:                   0.
% 2.19/0.95  
% 2.19/0.95  ------ QBF
% 2.19/0.95  
% 2.19/0.95  qbf_q_res:                              0
% 2.19/0.95  qbf_num_tautologies:                    0
% 2.19/0.95  qbf_prep_cycles:                        0
% 2.19/0.95  
% 2.19/0.95  ------ BMC1
% 2.19/0.95  
% 2.19/0.95  bmc1_current_bound:                     -1
% 2.19/0.95  bmc1_last_solved_bound:                 -1
% 2.19/0.95  bmc1_unsat_core_size:                   -1
% 2.19/0.95  bmc1_unsat_core_parents_size:           -1
% 2.19/0.95  bmc1_merge_next_fun:                    0
% 2.19/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.95  
% 2.19/0.95  ------ Instantiation
% 2.19/0.95  
% 2.19/0.95  inst_num_of_clauses:                    511
% 2.19/0.95  inst_num_in_passive:                    84
% 2.19/0.95  inst_num_in_active:                     245
% 2.19/0.95  inst_num_in_unprocessed:                182
% 2.19/0.95  inst_num_of_loops:                      270
% 2.19/0.95  inst_num_of_learning_restarts:          0
% 2.19/0.95  inst_num_moves_active_passive:          21
% 2.19/0.95  inst_lit_activity:                      0
% 2.19/0.95  inst_lit_activity_moves:                0
% 2.19/0.95  inst_num_tautologies:                   0
% 2.19/0.95  inst_num_prop_implied:                  0
% 2.19/0.95  inst_num_existing_simplified:           0
% 2.19/0.95  inst_num_eq_res_simplified:             0
% 2.19/0.95  inst_num_child_elim:                    0
% 2.19/0.95  inst_num_of_dismatching_blockings:      137
% 2.19/0.95  inst_num_of_non_proper_insts:           404
% 2.19/0.95  inst_num_of_duplicates:                 0
% 2.19/0.95  inst_inst_num_from_inst_to_res:         0
% 2.19/0.95  inst_dismatching_checking_time:         0.
% 2.19/0.95  
% 2.19/0.95  ------ Resolution
% 2.19/0.95  
% 2.19/0.95  res_num_of_clauses:                     0
% 2.19/0.95  res_num_in_passive:                     0
% 2.19/0.95  res_num_in_active:                      0
% 2.19/0.95  res_num_of_loops:                       129
% 2.19/0.95  res_forward_subset_subsumed:            45
% 2.19/0.95  res_backward_subset_subsumed:           4
% 2.19/0.95  res_forward_subsumed:                   0
% 2.19/0.95  res_backward_subsumed:                  0
% 2.19/0.95  res_forward_subsumption_resolution:     0
% 2.19/0.95  res_backward_subsumption_resolution:    0
% 2.19/0.95  res_clause_to_clause_subsumption:       61
% 2.19/0.95  res_orphan_elimination:                 0
% 2.19/0.95  res_tautology_del:                      32
% 2.19/0.95  res_num_eq_res_simplified:              0
% 2.19/0.95  res_num_sel_changes:                    0
% 2.19/0.95  res_moves_from_active_to_pass:          0
% 2.19/0.95  
% 2.19/0.95  ------ Superposition
% 2.19/0.95  
% 2.19/0.95  sup_time_total:                         0.
% 2.19/0.95  sup_time_generating:                    0.
% 2.19/0.95  sup_time_sim_full:                      0.
% 2.19/0.95  sup_time_sim_immed:                     0.
% 2.19/0.95  
% 2.19/0.95  sup_num_of_clauses:                     31
% 2.19/0.95  sup_num_in_active:                      28
% 2.19/0.95  sup_num_in_passive:                     3
% 2.19/0.95  sup_num_of_loops:                       53
% 2.19/0.95  sup_fw_superposition:                   9
% 2.19/0.95  sup_bw_superposition:                   26
% 2.19/0.95  sup_immediate_simplified:               17
% 2.19/0.95  sup_given_eliminated:                   0
% 2.19/0.95  comparisons_done:                       0
% 2.19/0.95  comparisons_avoided:                    3
% 2.19/0.95  
% 2.19/0.95  ------ Simplifications
% 2.19/0.95  
% 2.19/0.95  
% 2.19/0.95  sim_fw_subset_subsumed:                 16
% 2.19/0.95  sim_bw_subset_subsumed:                 4
% 2.19/0.95  sim_fw_subsumed:                        0
% 2.19/0.95  sim_bw_subsumed:                        0
% 2.19/0.95  sim_fw_subsumption_res:                 0
% 2.19/0.95  sim_bw_subsumption_res:                 0
% 2.19/0.95  sim_tautology_del:                      0
% 2.19/0.95  sim_eq_tautology_del:                   0
% 2.19/0.95  sim_eq_res_simp:                        0
% 2.19/0.95  sim_fw_demodulated:                     1
% 2.19/0.95  sim_bw_demodulated:                     22
% 2.19/0.95  sim_light_normalised:                   12
% 2.19/0.95  sim_joinable_taut:                      0
% 2.19/0.95  sim_joinable_simp:                      0
% 2.19/0.95  sim_ac_normalised:                      0
% 2.19/0.95  sim_smt_subsumption:                    0
% 2.19/0.95  
%------------------------------------------------------------------------------
