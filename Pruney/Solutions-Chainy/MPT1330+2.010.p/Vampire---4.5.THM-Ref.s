%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 932 expanded)
%              Number of leaves         :   14 ( 323 expanded)
%              Depth                    :   26
%              Number of atoms          :  330 (6292 expanded)
%              Number of equality atoms :   94 (2411 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,plain,(
    $false ),
    inference(subsumption_resolution,[],[f361,f106])).

fof(f106,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f361,plain,(
    ~ v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f359,f272])).

fof(f272,plain,(
    v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f271,f134])).

fof(f134,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f133,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f133,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f132,f81])).

fof(f81,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(superposition,[],[f127,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = X0
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f41,f40])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f127,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k2_struct_0(sK1))
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f119,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(superposition,[],[f63,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f37,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f119,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k2_struct_0(sK1))
    | k1_xboole_0 != k2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    inference(superposition,[],[f85,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f85,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(superposition,[],[f62,f38])).

fof(f62,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f39,f42])).

fof(f39,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f271,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f270,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f270,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f252,f67])).

fof(f67,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f36,f42])).

fof(f36,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f252,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f44,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f37,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f359,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK2,X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK2,X0)
      | ~ v4_relat_1(sK2,X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(condensation,[],[f357])).

fof(f357,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK2,X1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_partfun1(sK2,X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f356,f324])).

fof(f324,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_partfun1(sK2,X1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_partfun1(sK2,X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(superposition,[],[f319,f319])).

% (7657)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f319,plain,(
    ! [X3] :
      ( u1_struct_0(sK0) = X3
      | ~ v1_partfun1(sK2,X3)
      | ~ v4_relat_1(sK2,X3) ) ),
    inference(subsumption_resolution,[],[f318,f81])).

fof(f318,plain,(
    ! [X3] :
      ( u1_struct_0(sK0) = X3
      | ~ v1_relat_1(sK2)
      | ~ v1_partfun1(sK2,X3)
      | ~ v4_relat_1(sK2,X3) ) ),
    inference(subsumption_resolution,[],[f312,f106])).

fof(f312,plain,(
    ! [X3] :
      ( u1_struct_0(sK0) = X3
      | ~ v4_relat_1(sK2,u1_struct_0(sK0))
      | ~ v1_relat_1(sK2)
      | ~ v1_partfun1(sK2,X3)
      | ~ v4_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f117,f272])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X2)
      | X1 = X2
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v1_partfun1(X0,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f356,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_partfun1(sK2,X1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_partfun1(sK2,X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f354,f81])).

fof(f354,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_partfun1(sK2,X1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_partfun1(sK2,X0)
      | ~ v4_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f350,f45])).

fof(f350,plain,(
    ! [X9] :
      ( k1_relat_1(sK2) != X9
      | ~ v1_partfun1(sK2,X9)
      | ~ v4_relat_1(sK2,X9) ) ),
    inference(superposition,[],[f155,f323])).

fof(f323,plain,(
    ! [X5] :
      ( k2_struct_0(sK0) = X5
      | ~ v1_partfun1(sK2,X5)
      | ~ v4_relat_1(sK2,X5) ) ),
    inference(subsumption_resolution,[],[f322,f81])).

fof(f322,plain,(
    ! [X5] :
      ( k2_struct_0(sK0) = X5
      | ~ v1_relat_1(sK2)
      | ~ v1_partfun1(sK2,X5)
      | ~ v4_relat_1(sK2,X5) ) ),
    inference(subsumption_resolution,[],[f314,f105])).

fof(f105,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f49,f63])).

fof(f314,plain,(
    ! [X5] :
      ( k2_struct_0(sK0) = X5
      | ~ v4_relat_1(sK2,k2_struct_0(sK0))
      | ~ v1_relat_1(sK2)
      | ~ v1_partfun1(sK2,X5)
      | ~ v4_relat_1(sK2,X5) ) ),
    inference(resolution,[],[f117,f269])).

fof(f269,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f268,f134])).

fof(f268,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f267,f35])).

fof(f267,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f251,f70])).

fof(f70,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f69,f34])).

fof(f69,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f64,f42])).

fof(f64,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f36,f42])).

fof(f251,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f44,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f74,f34])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f63,f42])).

fof(f155,plain,(
    k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f154,f66])).

fof(f154,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(superposition,[],[f152,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f152,plain,(
    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f145,f66])).

fof(f145,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(superposition,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f65,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f59,f34])).

fof(f59,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f39,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (7665)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.43  % (7665)Refutation not found, incomplete strategy% (7665)------------------------------
% 0.19/0.43  % (7665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (7665)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (7665)Memory used [KB]: 1663
% 0.19/0.43  % (7665)Time elapsed: 0.005 s
% 0.19/0.43  % (7665)------------------------------
% 0.19/0.43  % (7665)------------------------------
% 0.19/0.46  % (7670)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.47  % (7650)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (7670)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f367,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f361,f106])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.19/0.47    inference(resolution,[],[f49,f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30,f29,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,negated_conjecture,(
% 0.19/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.19/0.47    inference(negated_conjecture,[],[f11])).
% 0.19/0.47  fof(f11,conjecture,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f361,plain,(
% 0.19/0.47    ~v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.19/0.47    inference(resolution,[],[f359,f272])).
% 0.19/0.47  fof(f272,plain,(
% 0.19/0.47    v1_partfun1(sK2,u1_struct_0(sK0))),
% 0.19/0.47    inference(subsumption_resolution,[],[f271,f134])).
% 0.19/0.47  fof(f134,plain,(
% 0.19/0.47    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f133,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.47  fof(f133,plain,(
% 0.19/0.47    k1_xboole_0 != k2_struct_0(sK1) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f132,f81])).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    v1_relat_1(sK2)),
% 0.19/0.47    inference(resolution,[],[f47,f37])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.47  fof(f132,plain,(
% 0.19/0.47    k1_xboole_0 != k2_struct_0(sK1) | ~v1_relat_1(sK2) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f131])).
% 0.19/0.47  fof(f131,plain,(
% 0.19/0.47    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK1) | ~v1_relat_1(sK2) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(superposition,[],[f127,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = X0 | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) )),
% 0.19/0.47    inference(superposition,[],[f41,f40])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    k1_xboole_0 != k10_relat_1(sK2,k2_struct_0(sK1)) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.19/0.47    inference(subsumption_resolution,[],[f119,f73])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f63,f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    inference(subsumption_resolution,[],[f57,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    l1_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0)),
% 0.19/0.47    inference(superposition,[],[f37,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    k1_xboole_0 != k10_relat_1(sK2,k2_struct_0(sK1)) | k1_xboole_0 != k2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))),
% 0.19/0.47    inference(superposition,[],[f85,f52])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f62,f38])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f56,f33])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~l1_struct_0(sK0)),
% 0.19/0.47    inference(superposition,[],[f39,f42])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f271,plain,(
% 0.19/0.47    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f270,f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f270,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f252,f67])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f61,f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    l1_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f36,f42])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f252,plain,(
% 0.19/0.47    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(resolution,[],[f44,f66])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.47    inference(subsumption_resolution,[],[f60,f34])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f37,f42])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.47    inference(flattening,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.47  fof(f359,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f358])).
% 0.19/0.47  fof(f358,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v4_relat_1(sK2,X0)) )),
% 0.19/0.47    inference(condensation,[],[f357])).
% 0.19/0.47  fof(f357,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f356,f324])).
% 0.19/0.47  fof(f324,plain,(
% 0.19/0.47    ( ! [X0,X1] : (X0 = X1 | ~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) )),
% 0.19/0.47    inference(superposition,[],[f319,f319])).
% 0.19/0.47  % (7657)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  fof(f319,plain,(
% 0.19/0.47    ( ! [X3] : (u1_struct_0(sK0) = X3 | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f318,f81])).
% 0.19/0.47  fof(f318,plain,(
% 0.19/0.47    ( ! [X3] : (u1_struct_0(sK0) = X3 | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f312,f106])).
% 0.19/0.47  fof(f312,plain,(
% 0.19/0.47    ( ! [X3] : (u1_struct_0(sK0) = X3 | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3)) )),
% 0.19/0.47    inference(resolution,[],[f117,f272])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X2) | X1 = X2 | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f114])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (X1 = X2 | ~v1_partfun1(X0,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(superposition,[],[f45,f45])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.47  fof(f356,plain,(
% 0.19/0.47    ( ! [X0,X1] : (X0 != X1 | ~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f354,f81])).
% 0.19/0.47  fof(f354,plain,(
% 0.19/0.47    ( ! [X0,X1] : (X0 != X1 | ~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.19/0.47    inference(superposition,[],[f350,f45])).
% 0.19/0.47  fof(f350,plain,(
% 0.19/0.47    ( ! [X9] : (k1_relat_1(sK2) != X9 | ~v1_partfun1(sK2,X9) | ~v4_relat_1(sK2,X9)) )),
% 0.19/0.47    inference(superposition,[],[f155,f323])).
% 0.19/0.47  fof(f323,plain,(
% 0.19/0.47    ( ! [X5] : (k2_struct_0(sK0) = X5 | ~v1_partfun1(sK2,X5) | ~v4_relat_1(sK2,X5)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f322,f81])).
% 0.19/0.47  fof(f322,plain,(
% 0.19/0.47    ( ! [X5] : (k2_struct_0(sK0) = X5 | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X5) | ~v4_relat_1(sK2,X5)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f314,f105])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.19/0.47    inference(resolution,[],[f49,f63])).
% 0.19/0.47  fof(f314,plain,(
% 0.19/0.47    ( ! [X5] : (k2_struct_0(sK0) = X5 | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X5) | ~v4_relat_1(sK2,X5)) )),
% 0.19/0.47    inference(resolution,[],[f117,f269])).
% 0.19/0.47  fof(f269,plain,(
% 0.19/0.47    v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.19/0.47    inference(subsumption_resolution,[],[f268,f134])).
% 0.19/0.47  fof(f268,plain,(
% 0.19/0.47    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f267,f35])).
% 0.19/0.47  fof(f267,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f251,f70])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f69,f34])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f64,f42])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f58,f33])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~l1_struct_0(sK0)),
% 0.19/0.47    inference(superposition,[],[f36,f42])).
% 0.19/0.47  fof(f251,plain,(
% 0.19/0.47    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    inference(resolution,[],[f44,f75])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.47    inference(subsumption_resolution,[],[f74,f34])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f63,f42])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relat_1(sK2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f154,f66])).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.47    inference(superposition,[],[f152,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f145,f66])).
% 0.19/0.47  fof(f145,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.47    inference(superposition,[],[f65,f51])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f59,f34])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.19/0.47    inference(superposition,[],[f39,f42])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (7670)------------------------------
% 0.19/0.47  % (7670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (7670)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (7670)Memory used [KB]: 1791
% 0.19/0.47  % (7670)Time elapsed: 0.045 s
% 0.19/0.47  % (7670)------------------------------
% 0.19/0.47  % (7670)------------------------------
% 0.19/0.47  % (7650)Refutation not found, incomplete strategy% (7650)------------------------------
% 0.19/0.47  % (7650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (7650)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (7650)Memory used [KB]: 10618
% 0.19/0.47  % (7650)Time elapsed: 0.060 s
% 0.19/0.47  % (7650)------------------------------
% 0.19/0.47  % (7650)------------------------------
% 0.19/0.47  % (7646)Success in time 0.117 s
%------------------------------------------------------------------------------
