%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1417+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:54 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  155 (1837 expanded)
%              Number of leaves         :   11 ( 756 expanded)
%              Depth                    :   25
%              Number of atoms          :  764 (14811 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(subsumption_resolution,[],[f293,f149])).

fof(f149,plain,(
    v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f148,f30])).

fof(f30,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r6_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m2_filter_1(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r6_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m2_filter_1(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r6_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m2_filter_1(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                & r6_binop_1(sK0,X2,X3)
                & m2_filter_1(X3,sK0,X1) )
            & m2_filter_1(X2,sK0,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
              & r6_binop_1(sK0,X2,X3)
              & m2_filter_1(X3,sK0,sK1) )
          & m2_filter_1(X2,sK0,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v8_relat_2(sK1)
      & v3_relat_2(sK1)
      & v1_partfun1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
            & r6_binop_1(sK0,X2,X3)
            & m2_filter_1(X3,sK0,sK1) )
        & m2_filter_1(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
          & r6_binop_1(sK0,sK2,X3)
          & m2_filter_1(X3,sK0,sK1) )
      & m2_filter_1(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r6_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r6_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r6_binop_1(X0,X2,X3)
                     => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r6_binop_1(X0,X2,X3)
                   => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_filter_1)).

fof(f148,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK2))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f31,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK2))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f146,f32])).

fof(f32,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f146,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK2))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f111,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v1_funct_1(k3_filter_1(sK0,X5,sK2))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,X5,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f53,plain,
    ( v1_funct_1(sK2)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f51,f50])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,
    ( v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    m2_filter_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f109,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,X5,sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f60])).

fof(f60,plain,(
    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f50])).

fof(f57,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f41,f34])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,X5,sK2))
      | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f63,f50])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f293,plain,(
    ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f292,f193])).

fof(f193,plain,(
    v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f192,f30])).

fof(f192,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f191,f31])).

fof(f191,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f190,f32])).

fof(f190,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f102,f33])).

fof(f102,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v1_funct_2(k3_filter_1(sK0,X1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f101,f29])).

fof(f101,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK0,X1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f100,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK0,X1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f60])).

fof(f89,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK0,X1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f292,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f291,f179])).

fof(f179,plain,(
    r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f160,f178])).

fof(f178,plain,(
    r5_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f177,f54])).

fof(f177,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f60])).

fof(f176,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f36,plain,(
    r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f174,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f130,f66])).

fof(f130,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | r5_binop_1(sK0,X3,sK3)
      | ~ r6_binop_1(sK0,X3,sK3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f55,f29])).

fof(f55,plain,
    ( v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f52,f50])).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,(
    ! [X3] :
      ( ~ r6_binop_1(sK0,X3,sK3)
      | r5_binop_1(sK0,X3,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f115,f62])).

fof(f62,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f61,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f58,f50])).

fof(f58,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f41,f35])).

fof(f115,plain,(
    ! [X3] :
      ( ~ r6_binop_1(sK0,X3,sK3)
      | r5_binop_1(sK0,X3,sK3)
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r6_binop_1(X0,X1,X2)
      | r5_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_binop_1)).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f50])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f35])).

fof(f160,plain,
    ( ~ r5_binop_1(sK0,sK2,sK3)
    | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f139,f34])).

fof(f139,plain,(
    ! [X1] :
      ( ~ m2_filter_1(X1,sK0,sK1)
      | ~ r5_binop_1(sK0,X1,sK3)
      | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f80,f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m2_filter_1(X1,sK0,sK1)
      | ~ r5_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f79,f29])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r5_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r5_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r5_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r5_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f39,f33])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r5_binop_1(X0,X2,X3)
                   => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_filter_1)).

fof(f291,plain,
    ( ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f290,f37])).

fof(f37,plain,(
    ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f290,plain,
    ( r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f288,f187])).

fof(f187,plain,(
    r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f156,f186])).

fof(f186,plain,(
    r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f185,f54])).

fof(f185,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f184,f60])).

fof(f184,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f182,f36])).

fof(f182,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f132,f66])).

fof(f132,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | r4_binop_1(sK0,X4,sK3)
      | ~ r6_binop_1(sK0,X4,sK3)
      | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f131,plain,(
    ! [X4] :
      ( ~ r6_binop_1(sK0,X4,sK3)
      | r4_binop_1(sK0,X4,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f116,f62])).

fof(f116,plain,(
    ! [X4] :
      ( ~ r6_binop_1(sK0,X4,sK3)
      | r4_binop_1(sK0,X4,sK3)
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X4) ) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r6_binop_1(X0,X1,X2)
      | r4_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f156,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f137,f34])).

fof(f137,plain,(
    ! [X1] :
      ( ~ m2_filter_1(X1,sK0,sK1)
      | ~ r4_binop_1(sK0,X1,sK3)
      | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m2_filter_1(X1,sK0,sK1)
      | ~ r4_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r4_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f73,f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r4_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f31])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r4_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f71,f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r4_binop_1(sK0,X0,X1)
      | ~ m2_filter_1(X1,sK0,sK1)
      | ~ m2_filter_1(X0,sK0,sK1)
      | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r4_binop_1(X0,X2,X3)
                   => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_filter_1)).

fof(f288,plain,
    ( ~ r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f255,f211])).

fof(f211,plain,(
    m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f210,f30])).

fof(f210,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f209,f31])).

fof(f209,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f208,f32])).

fof(f208,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f99,f33])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | m1_subset_1(k3_filter_1(sK0,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f98,f29])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(k3_filter_1(sK0,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f54])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(k3_filter_1(sK0,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f60])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(k3_filter_1(sK0,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f255,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ r4_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | r6_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | ~ r5_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | ~ v1_funct_2(X2,k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f254,f153])).

fof(f153,plain,(
    v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f152,f30])).

fof(f152,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f151,f31])).

fof(f151,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f150,f32])).

fof(f150,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f135,f33])).

fof(f135,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v1_funct_1(k3_filter_1(sK0,X5,sK3))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f134,f29])).

fof(f134,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,X5,sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f56])).

fof(f133,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,X5,sK3))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f62])).

fof(f117,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,X5,sK3))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f68,f47])).

fof(f254,plain,(
    ! [X2] :
      ( ~ r5_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | ~ r4_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | r6_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f243,f203])).

fof(f203,plain,(
    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f202,f30])).

fof(f202,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f201,f31])).

fof(f201,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f200,f32])).

fof(f200,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f126,f33])).

fof(f126,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v1_funct_2(k3_filter_1(sK0,X1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f125,f29])).

fof(f125,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK0,X1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f56])).

fof(f124,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK0,X1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f62])).

fof(f113,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK0,X1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,X1),k8_eqrel_1(sK0,X1)),k8_eqrel_1(sK0,X1))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f68,f48])).

fof(f243,plain,(
    ! [X2] :
      ( ~ r5_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | ~ r4_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | r6_binop_1(k8_eqrel_1(sK0,sK1),X2,k3_filter_1(sK0,sK1,sK3))
      | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f215,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r5_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | r6_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f215,plain,(
    m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f214,f30])).

fof(f214,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f213,f31])).

fof(f213,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f212,f32])).

fof(f212,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f123,f33])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | m1_subset_1(k3_filter_1(sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f122,f29])).

fof(f122,plain,(
    ! [X0] :
      ( m1_subset_1(k3_filter_1(sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f56])).

fof(f121,plain,(
    ! [X0] :
      ( m1_subset_1(k3_filter_1(sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f62])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(k3_filter_1(sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,X0),k8_eqrel_1(sK0,X0)),k8_eqrel_1(sK0,X0))))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f68,f49])).

%------------------------------------------------------------------------------
