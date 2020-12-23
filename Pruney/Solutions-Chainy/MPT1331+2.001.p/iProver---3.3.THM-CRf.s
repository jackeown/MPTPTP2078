%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:59 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 639 expanded)
%              Number of clauses        :   83 ( 188 expanded)
%              Number of leaves         :   16 ( 197 expanded)
%              Depth                    :   26
%              Number of atoms          :  404 (3471 expanded)
%              Number of equality atoms :   89 ( 215 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f37,f36,f35,f34])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k3_funct_3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_865,plain,
    ( r1_tarski(k9_relat_1(X0_50,X1_50),k2_relat_1(X0_50))
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1268,plain,
    ( r1_tarski(k9_relat_1(X0_50,X1_50),k2_relat_1(X0_50)) = iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_865])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_861,plain,
    ( r1_tarski(k2_relat_1(k3_funct_3(X0_50)),k1_zfmisc_1(k1_relat_1(X0_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1272,plain,
    ( r1_tarski(k2_relat_1(k3_funct_3(X0_50)),k1_zfmisc_1(k1_relat_1(X0_50))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_867,plain,
    ( ~ r1_tarski(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1266,plain,
    ( r1_tarski(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_421,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_422,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_852,plain,
    ( ~ r1_tarski(X0_50,X1_50)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_1279,plain,
    ( r1_tarski(X0_50,X1_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_403,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_404,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_854,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_1342,plain,
    ( r1_tarski(X0_50,X1_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1279,c_854])).

cnf(c_1724,plain,
    ( r1_tarski(X0_50,X1_50) != iProver_top
    | r1_tarski(X1_50,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1342])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_858,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1275,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_398,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_399,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_855,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_1289,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1275,c_854,c_855])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_337,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_8])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_8,c_4,c_3])).

cnf(c_342,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_295,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_296,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_42,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_298,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_21,c_20,c_42])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_308,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_309,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_311,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_19,c_17])).

cnf(c_312,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_325,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_298,c_312])).

cnf(c_45,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_327,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_20,c_45])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_342,c_327])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_856,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50)))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_1277,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_1311,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_50))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1277,c_854])).

cnf(c_1312,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_50))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1311,c_854])).

cnf(c_1476,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1289,c_1312])).

cnf(c_2118,plain,
    ( r1_tarski(X0_50,X1_50) != iProver_top
    | r1_tarski(X1_50,k1_zfmisc_1(k1_relat_1(sK2))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1724,c_1476])).

cnf(c_2125,plain,
    ( r1_tarski(X0_50,k2_relat_1(k3_funct_3(sK2))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_2118])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1394,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_1395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_2490,plain,
    ( r1_tarski(X0_50,k2_relat_1(k3_funct_3(sK2))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2125,c_26,c_28,c_1395])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_866,plain,
    ( r1_tarski(X0_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1267,plain,
    ( r1_tarski(X0_50,X1_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_2498,plain,
    ( r1_tarski(X0_50,k2_relat_1(k3_funct_3(sK2))) != iProver_top
    | r1_tarski(X0_50,k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_1267])).

cnf(c_2521,plain,
    ( r1_tarski(k9_relat_1(k3_funct_3(sK2),X0_50),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top
    | v1_relat_1(k3_funct_3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1268,c_2498])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k3_funct_3(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_862,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(k3_funct_3(X0_50)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_908,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k3_funct_3(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_910,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k3_funct_3(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_2562,plain,
    ( r1_tarski(k9_relat_1(k3_funct_3(sK2),X0_50),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2521,c_26,c_28,c_910,c_1395])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_860,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1273,plain,
    ( m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_1292,plain,
    ( m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1273,c_854])).

cnf(c_1558,plain,
    ( r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1292])).

cnf(c_1963,plain,
    ( r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_relat_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1558,c_1476])).

cnf(c_2570,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2562,c_1963])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.92/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.92/1.02  
% 0.92/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.92/1.02  
% 0.92/1.02  ------  iProver source info
% 0.92/1.02  
% 0.92/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.92/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.92/1.02  git: non_committed_changes: false
% 0.92/1.02  git: last_make_outside_of_git: false
% 0.92/1.02  
% 0.92/1.02  ------ 
% 0.92/1.02  
% 0.92/1.02  ------ Input Options
% 0.92/1.02  
% 0.92/1.02  --out_options                           all
% 0.92/1.02  --tptp_safe_out                         true
% 0.92/1.02  --problem_path                          ""
% 0.92/1.02  --include_path                          ""
% 0.92/1.02  --clausifier                            res/vclausify_rel
% 0.92/1.02  --clausifier_options                    --mode clausify
% 0.92/1.02  --stdin                                 false
% 0.92/1.02  --stats_out                             all
% 0.92/1.02  
% 0.92/1.02  ------ General Options
% 0.92/1.02  
% 0.92/1.02  --fof                                   false
% 0.92/1.02  --time_out_real                         305.
% 0.92/1.02  --time_out_virtual                      -1.
% 0.92/1.02  --symbol_type_check                     false
% 0.92/1.02  --clausify_out                          false
% 0.92/1.02  --sig_cnt_out                           false
% 0.92/1.02  --trig_cnt_out                          false
% 0.92/1.02  --trig_cnt_out_tolerance                1.
% 0.92/1.02  --trig_cnt_out_sk_spl                   false
% 0.92/1.02  --abstr_cl_out                          false
% 0.92/1.02  
% 0.92/1.02  ------ Global Options
% 0.92/1.02  
% 0.92/1.02  --schedule                              default
% 0.92/1.02  --add_important_lit                     false
% 0.92/1.02  --prop_solver_per_cl                    1000
% 0.92/1.02  --min_unsat_core                        false
% 0.92/1.02  --soft_assumptions                      false
% 0.92/1.02  --soft_lemma_size                       3
% 0.92/1.02  --prop_impl_unit_size                   0
% 0.92/1.02  --prop_impl_unit                        []
% 0.92/1.02  --share_sel_clauses                     true
% 0.92/1.02  --reset_solvers                         false
% 0.92/1.02  --bc_imp_inh                            [conj_cone]
% 0.92/1.02  --conj_cone_tolerance                   3.
% 0.92/1.02  --extra_neg_conj                        none
% 0.92/1.02  --large_theory_mode                     true
% 0.92/1.02  --prolific_symb_bound                   200
% 0.92/1.02  --lt_threshold                          2000
% 0.92/1.02  --clause_weak_htbl                      true
% 0.92/1.02  --gc_record_bc_elim                     false
% 0.92/1.02  
% 0.92/1.02  ------ Preprocessing Options
% 0.92/1.02  
% 0.92/1.02  --preprocessing_flag                    true
% 0.92/1.02  --time_out_prep_mult                    0.1
% 0.92/1.02  --splitting_mode                        input
% 0.92/1.02  --splitting_grd                         true
% 0.92/1.02  --splitting_cvd                         false
% 0.92/1.02  --splitting_cvd_svl                     false
% 0.92/1.02  --splitting_nvd                         32
% 0.92/1.02  --sub_typing                            true
% 0.92/1.02  --prep_gs_sim                           true
% 0.92/1.02  --prep_unflatten                        true
% 0.92/1.02  --prep_res_sim                          true
% 0.92/1.02  --prep_upred                            true
% 0.92/1.02  --prep_sem_filter                       exhaustive
% 0.92/1.02  --prep_sem_filter_out                   false
% 0.92/1.02  --pred_elim                             true
% 0.92/1.02  --res_sim_input                         true
% 0.92/1.02  --eq_ax_congr_red                       true
% 0.92/1.02  --pure_diseq_elim                       true
% 0.92/1.02  --brand_transform                       false
% 0.92/1.02  --non_eq_to_eq                          false
% 0.92/1.02  --prep_def_merge                        true
% 0.92/1.02  --prep_def_merge_prop_impl              false
% 0.92/1.02  --prep_def_merge_mbd                    true
% 0.92/1.02  --prep_def_merge_tr_red                 false
% 0.92/1.02  --prep_def_merge_tr_cl                  false
% 0.92/1.02  --smt_preprocessing                     true
% 0.92/1.02  --smt_ac_axioms                         fast
% 0.92/1.02  --preprocessed_out                      false
% 0.92/1.02  --preprocessed_stats                    false
% 0.92/1.02  
% 0.92/1.02  ------ Abstraction refinement Options
% 0.92/1.02  
% 0.92/1.02  --abstr_ref                             []
% 0.92/1.02  --abstr_ref_prep                        false
% 0.92/1.02  --abstr_ref_until_sat                   false
% 0.92/1.02  --abstr_ref_sig_restrict                funpre
% 0.92/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/1.02  --abstr_ref_under                       []
% 0.92/1.02  
% 0.92/1.02  ------ SAT Options
% 0.92/1.02  
% 0.92/1.02  --sat_mode                              false
% 0.92/1.02  --sat_fm_restart_options                ""
% 0.92/1.02  --sat_gr_def                            false
% 0.92/1.02  --sat_epr_types                         true
% 0.92/1.02  --sat_non_cyclic_types                  false
% 0.92/1.02  --sat_finite_models                     false
% 0.92/1.02  --sat_fm_lemmas                         false
% 0.92/1.02  --sat_fm_prep                           false
% 0.92/1.02  --sat_fm_uc_incr                        true
% 0.92/1.02  --sat_out_model                         small
% 0.92/1.02  --sat_out_clauses                       false
% 0.92/1.02  
% 0.92/1.02  ------ QBF Options
% 0.92/1.02  
% 0.92/1.02  --qbf_mode                              false
% 0.92/1.02  --qbf_elim_univ                         false
% 0.92/1.02  --qbf_dom_inst                          none
% 0.92/1.02  --qbf_dom_pre_inst                      false
% 0.92/1.02  --qbf_sk_in                             false
% 0.92/1.02  --qbf_pred_elim                         true
% 0.92/1.02  --qbf_split                             512
% 0.92/1.02  
% 0.92/1.02  ------ BMC1 Options
% 0.92/1.02  
% 0.92/1.02  --bmc1_incremental                      false
% 0.92/1.02  --bmc1_axioms                           reachable_all
% 0.92/1.02  --bmc1_min_bound                        0
% 0.92/1.02  --bmc1_max_bound                        -1
% 0.92/1.02  --bmc1_max_bound_default                -1
% 0.92/1.02  --bmc1_symbol_reachability              true
% 0.92/1.02  --bmc1_property_lemmas                  false
% 0.92/1.02  --bmc1_k_induction                      false
% 0.92/1.02  --bmc1_non_equiv_states                 false
% 0.92/1.02  --bmc1_deadlock                         false
% 0.92/1.02  --bmc1_ucm                              false
% 0.92/1.02  --bmc1_add_unsat_core                   none
% 0.92/1.02  --bmc1_unsat_core_children              false
% 0.92/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/1.02  --bmc1_out_stat                         full
% 0.92/1.02  --bmc1_ground_init                      false
% 0.92/1.02  --bmc1_pre_inst_next_state              false
% 0.92/1.02  --bmc1_pre_inst_state                   false
% 0.92/1.02  --bmc1_pre_inst_reach_state             false
% 0.92/1.02  --bmc1_out_unsat_core                   false
% 0.92/1.02  --bmc1_aig_witness_out                  false
% 0.92/1.02  --bmc1_verbose                          false
% 0.92/1.02  --bmc1_dump_clauses_tptp                false
% 0.92/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.92/1.02  --bmc1_dump_file                        -
% 0.92/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.92/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.92/1.02  --bmc1_ucm_extend_mode                  1
% 0.92/1.02  --bmc1_ucm_init_mode                    2
% 0.92/1.02  --bmc1_ucm_cone_mode                    none
% 0.92/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.92/1.02  --bmc1_ucm_relax_model                  4
% 0.92/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.92/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/1.02  --bmc1_ucm_layered_model                none
% 0.92/1.02  --bmc1_ucm_max_lemma_size               10
% 0.92/1.02  
% 0.92/1.02  ------ AIG Options
% 0.92/1.02  
% 0.92/1.02  --aig_mode                              false
% 0.92/1.02  
% 0.92/1.02  ------ Instantiation Options
% 0.92/1.02  
% 0.92/1.02  --instantiation_flag                    true
% 0.92/1.02  --inst_sos_flag                         false
% 0.92/1.02  --inst_sos_phase                        true
% 0.92/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/1.02  --inst_lit_sel_side                     num_symb
% 0.92/1.02  --inst_solver_per_active                1400
% 0.92/1.02  --inst_solver_calls_frac                1.
% 0.92/1.02  --inst_passive_queue_type               priority_queues
% 0.92/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/1.02  --inst_passive_queues_freq              [25;2]
% 0.92/1.02  --inst_dismatching                      true
% 0.92/1.02  --inst_eager_unprocessed_to_passive     true
% 0.92/1.02  --inst_prop_sim_given                   true
% 0.92/1.02  --inst_prop_sim_new                     false
% 0.92/1.02  --inst_subs_new                         false
% 0.92/1.02  --inst_eq_res_simp                      false
% 0.92/1.02  --inst_subs_given                       false
% 0.92/1.02  --inst_orphan_elimination               true
% 0.92/1.02  --inst_learning_loop_flag               true
% 0.92/1.02  --inst_learning_start                   3000
% 0.92/1.02  --inst_learning_factor                  2
% 0.92/1.02  --inst_start_prop_sim_after_learn       3
% 0.92/1.02  --inst_sel_renew                        solver
% 0.92/1.02  --inst_lit_activity_flag                true
% 0.92/1.02  --inst_restr_to_given                   false
% 0.92/1.02  --inst_activity_threshold               500
% 0.92/1.02  --inst_out_proof                        true
% 0.92/1.02  
% 0.92/1.02  ------ Resolution Options
% 0.92/1.02  
% 0.92/1.02  --resolution_flag                       true
% 0.92/1.02  --res_lit_sel                           adaptive
% 0.92/1.02  --res_lit_sel_side                      none
% 0.92/1.02  --res_ordering                          kbo
% 0.92/1.02  --res_to_prop_solver                    active
% 0.92/1.02  --res_prop_simpl_new                    false
% 0.92/1.02  --res_prop_simpl_given                  true
% 0.92/1.02  --res_passive_queue_type                priority_queues
% 0.92/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/1.02  --res_passive_queues_freq               [15;5]
% 0.92/1.02  --res_forward_subs                      full
% 0.92/1.02  --res_backward_subs                     full
% 0.92/1.02  --res_forward_subs_resolution           true
% 0.92/1.02  --res_backward_subs_resolution          true
% 0.92/1.02  --res_orphan_elimination                true
% 0.92/1.02  --res_time_limit                        2.
% 0.92/1.02  --res_out_proof                         true
% 0.92/1.02  
% 0.92/1.02  ------ Superposition Options
% 0.92/1.02  
% 0.92/1.02  --superposition_flag                    true
% 0.92/1.02  --sup_passive_queue_type                priority_queues
% 0.92/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.92/1.02  --demod_completeness_check              fast
% 0.92/1.02  --demod_use_ground                      true
% 0.92/1.02  --sup_to_prop_solver                    passive
% 0.92/1.02  --sup_prop_simpl_new                    true
% 0.92/1.02  --sup_prop_simpl_given                  true
% 0.92/1.02  --sup_fun_splitting                     false
% 0.92/1.02  --sup_smt_interval                      50000
% 0.92/1.02  
% 0.92/1.02  ------ Superposition Simplification Setup
% 0.92/1.02  
% 0.92/1.02  --sup_indices_passive                   []
% 0.92/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.02  --sup_full_bw                           [BwDemod]
% 0.92/1.02  --sup_immed_triv                        [TrivRules]
% 0.92/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.02  --sup_immed_bw_main                     []
% 0.92/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.02  
% 0.92/1.02  ------ Combination Options
% 0.92/1.02  
% 0.92/1.02  --comb_res_mult                         3
% 0.92/1.02  --comb_sup_mult                         2
% 0.92/1.02  --comb_inst_mult                        10
% 0.92/1.02  
% 0.92/1.02  ------ Debug Options
% 0.92/1.02  
% 0.92/1.02  --dbg_backtrace                         false
% 0.92/1.02  --dbg_dump_prop_clauses                 false
% 0.92/1.02  --dbg_dump_prop_clauses_file            -
% 0.92/1.02  --dbg_out_stat                          false
% 0.92/1.02  ------ Parsing...
% 0.92/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.92/1.02  
% 0.92/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.92/1.02  
% 0.92/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.92/1.02  
% 0.92/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.92/1.02  ------ Proving...
% 0.92/1.02  ------ Problem Properties 
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  clauses                                 16
% 0.92/1.02  conjectures                             4
% 0.92/1.02  EPR                                     1
% 0.92/1.02  Horn                                    16
% 0.92/1.02  unary                                   6
% 0.92/1.02  binary                                  5
% 0.92/1.02  lits                                    31
% 0.92/1.02  lits eq                                 3
% 0.92/1.02  fd_pure                                 0
% 0.92/1.02  fd_pseudo                               0
% 0.92/1.02  fd_cond                                 0
% 0.92/1.02  fd_pseudo_cond                          0
% 0.92/1.02  AC symbols                              0
% 0.92/1.02  
% 0.92/1.02  ------ Schedule dynamic 5 is on 
% 0.92/1.02  
% 0.92/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  ------ 
% 0.92/1.02  Current options:
% 0.92/1.02  ------ 
% 0.92/1.02  
% 0.92/1.02  ------ Input Options
% 0.92/1.02  
% 0.92/1.02  --out_options                           all
% 0.92/1.02  --tptp_safe_out                         true
% 0.92/1.02  --problem_path                          ""
% 0.92/1.02  --include_path                          ""
% 0.92/1.02  --clausifier                            res/vclausify_rel
% 0.92/1.02  --clausifier_options                    --mode clausify
% 0.92/1.02  --stdin                                 false
% 0.92/1.02  --stats_out                             all
% 0.92/1.02  
% 0.92/1.02  ------ General Options
% 0.92/1.02  
% 0.92/1.02  --fof                                   false
% 0.92/1.02  --time_out_real                         305.
% 0.92/1.02  --time_out_virtual                      -1.
% 0.92/1.02  --symbol_type_check                     false
% 0.92/1.02  --clausify_out                          false
% 0.92/1.02  --sig_cnt_out                           false
% 0.92/1.02  --trig_cnt_out                          false
% 0.92/1.02  --trig_cnt_out_tolerance                1.
% 0.92/1.02  --trig_cnt_out_sk_spl                   false
% 0.92/1.02  --abstr_cl_out                          false
% 0.92/1.02  
% 0.92/1.02  ------ Global Options
% 0.92/1.02  
% 0.92/1.02  --schedule                              default
% 0.92/1.02  --add_important_lit                     false
% 0.92/1.02  --prop_solver_per_cl                    1000
% 0.92/1.02  --min_unsat_core                        false
% 0.92/1.02  --soft_assumptions                      false
% 0.92/1.02  --soft_lemma_size                       3
% 0.92/1.02  --prop_impl_unit_size                   0
% 0.92/1.02  --prop_impl_unit                        []
% 0.92/1.02  --share_sel_clauses                     true
% 0.92/1.02  --reset_solvers                         false
% 0.92/1.02  --bc_imp_inh                            [conj_cone]
% 0.92/1.02  --conj_cone_tolerance                   3.
% 0.92/1.02  --extra_neg_conj                        none
% 0.92/1.02  --large_theory_mode                     true
% 0.92/1.02  --prolific_symb_bound                   200
% 0.92/1.02  --lt_threshold                          2000
% 0.92/1.02  --clause_weak_htbl                      true
% 0.92/1.02  --gc_record_bc_elim                     false
% 0.92/1.02  
% 0.92/1.02  ------ Preprocessing Options
% 0.92/1.02  
% 0.92/1.02  --preprocessing_flag                    true
% 0.92/1.02  --time_out_prep_mult                    0.1
% 0.92/1.02  --splitting_mode                        input
% 0.92/1.02  --splitting_grd                         true
% 0.92/1.02  --splitting_cvd                         false
% 0.92/1.02  --splitting_cvd_svl                     false
% 0.92/1.02  --splitting_nvd                         32
% 0.92/1.02  --sub_typing                            true
% 0.92/1.02  --prep_gs_sim                           true
% 0.92/1.02  --prep_unflatten                        true
% 0.92/1.02  --prep_res_sim                          true
% 0.92/1.02  --prep_upred                            true
% 0.92/1.02  --prep_sem_filter                       exhaustive
% 0.92/1.02  --prep_sem_filter_out                   false
% 0.92/1.02  --pred_elim                             true
% 0.92/1.02  --res_sim_input                         true
% 0.92/1.02  --eq_ax_congr_red                       true
% 0.92/1.02  --pure_diseq_elim                       true
% 0.92/1.02  --brand_transform                       false
% 0.92/1.02  --non_eq_to_eq                          false
% 0.92/1.02  --prep_def_merge                        true
% 0.92/1.02  --prep_def_merge_prop_impl              false
% 0.92/1.02  --prep_def_merge_mbd                    true
% 0.92/1.02  --prep_def_merge_tr_red                 false
% 0.92/1.02  --prep_def_merge_tr_cl                  false
% 0.92/1.02  --smt_preprocessing                     true
% 0.92/1.02  --smt_ac_axioms                         fast
% 0.92/1.02  --preprocessed_out                      false
% 0.92/1.02  --preprocessed_stats                    false
% 0.92/1.02  
% 0.92/1.02  ------ Abstraction refinement Options
% 0.92/1.02  
% 0.92/1.02  --abstr_ref                             []
% 0.92/1.02  --abstr_ref_prep                        false
% 0.92/1.02  --abstr_ref_until_sat                   false
% 0.92/1.02  --abstr_ref_sig_restrict                funpre
% 0.92/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/1.02  --abstr_ref_under                       []
% 0.92/1.02  
% 0.92/1.02  ------ SAT Options
% 0.92/1.02  
% 0.92/1.02  --sat_mode                              false
% 0.92/1.02  --sat_fm_restart_options                ""
% 0.92/1.02  --sat_gr_def                            false
% 0.92/1.02  --sat_epr_types                         true
% 0.92/1.02  --sat_non_cyclic_types                  false
% 0.92/1.02  --sat_finite_models                     false
% 0.92/1.02  --sat_fm_lemmas                         false
% 0.92/1.02  --sat_fm_prep                           false
% 0.92/1.02  --sat_fm_uc_incr                        true
% 0.92/1.02  --sat_out_model                         small
% 0.92/1.02  --sat_out_clauses                       false
% 0.92/1.02  
% 0.92/1.02  ------ QBF Options
% 0.92/1.02  
% 0.92/1.02  --qbf_mode                              false
% 0.92/1.02  --qbf_elim_univ                         false
% 0.92/1.02  --qbf_dom_inst                          none
% 0.92/1.02  --qbf_dom_pre_inst                      false
% 0.92/1.02  --qbf_sk_in                             false
% 0.92/1.02  --qbf_pred_elim                         true
% 0.92/1.02  --qbf_split                             512
% 0.92/1.02  
% 0.92/1.02  ------ BMC1 Options
% 0.92/1.02  
% 0.92/1.02  --bmc1_incremental                      false
% 0.92/1.02  --bmc1_axioms                           reachable_all
% 0.92/1.02  --bmc1_min_bound                        0
% 0.92/1.02  --bmc1_max_bound                        -1
% 0.92/1.02  --bmc1_max_bound_default                -1
% 0.92/1.02  --bmc1_symbol_reachability              true
% 0.92/1.02  --bmc1_property_lemmas                  false
% 0.92/1.02  --bmc1_k_induction                      false
% 0.92/1.02  --bmc1_non_equiv_states                 false
% 0.92/1.02  --bmc1_deadlock                         false
% 0.92/1.02  --bmc1_ucm                              false
% 0.92/1.02  --bmc1_add_unsat_core                   none
% 0.92/1.02  --bmc1_unsat_core_children              false
% 0.92/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/1.02  --bmc1_out_stat                         full
% 0.92/1.02  --bmc1_ground_init                      false
% 0.92/1.02  --bmc1_pre_inst_next_state              false
% 0.92/1.02  --bmc1_pre_inst_state                   false
% 0.92/1.02  --bmc1_pre_inst_reach_state             false
% 0.92/1.02  --bmc1_out_unsat_core                   false
% 0.92/1.02  --bmc1_aig_witness_out                  false
% 0.92/1.02  --bmc1_verbose                          false
% 0.92/1.02  --bmc1_dump_clauses_tptp                false
% 0.92/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.92/1.02  --bmc1_dump_file                        -
% 0.92/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.92/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.92/1.02  --bmc1_ucm_extend_mode                  1
% 0.92/1.02  --bmc1_ucm_init_mode                    2
% 0.92/1.02  --bmc1_ucm_cone_mode                    none
% 0.92/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.92/1.02  --bmc1_ucm_relax_model                  4
% 0.92/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.92/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/1.02  --bmc1_ucm_layered_model                none
% 0.92/1.02  --bmc1_ucm_max_lemma_size               10
% 0.92/1.02  
% 0.92/1.02  ------ AIG Options
% 0.92/1.02  
% 0.92/1.02  --aig_mode                              false
% 0.92/1.02  
% 0.92/1.02  ------ Instantiation Options
% 0.92/1.02  
% 0.92/1.02  --instantiation_flag                    true
% 0.92/1.02  --inst_sos_flag                         false
% 0.92/1.02  --inst_sos_phase                        true
% 0.92/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/1.02  --inst_lit_sel_side                     none
% 0.92/1.02  --inst_solver_per_active                1400
% 0.92/1.02  --inst_solver_calls_frac                1.
% 0.92/1.02  --inst_passive_queue_type               priority_queues
% 0.92/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/1.02  --inst_passive_queues_freq              [25;2]
% 0.92/1.02  --inst_dismatching                      true
% 0.92/1.02  --inst_eager_unprocessed_to_passive     true
% 0.92/1.02  --inst_prop_sim_given                   true
% 0.92/1.02  --inst_prop_sim_new                     false
% 0.92/1.02  --inst_subs_new                         false
% 0.92/1.02  --inst_eq_res_simp                      false
% 0.92/1.02  --inst_subs_given                       false
% 0.92/1.02  --inst_orphan_elimination               true
% 0.92/1.02  --inst_learning_loop_flag               true
% 0.92/1.02  --inst_learning_start                   3000
% 0.92/1.02  --inst_learning_factor                  2
% 0.92/1.02  --inst_start_prop_sim_after_learn       3
% 0.92/1.02  --inst_sel_renew                        solver
% 0.92/1.02  --inst_lit_activity_flag                true
% 0.92/1.02  --inst_restr_to_given                   false
% 0.92/1.02  --inst_activity_threshold               500
% 0.92/1.02  --inst_out_proof                        true
% 0.92/1.02  
% 0.92/1.02  ------ Resolution Options
% 0.92/1.02  
% 0.92/1.02  --resolution_flag                       false
% 0.92/1.02  --res_lit_sel                           adaptive
% 0.92/1.02  --res_lit_sel_side                      none
% 0.92/1.02  --res_ordering                          kbo
% 0.92/1.02  --res_to_prop_solver                    active
% 0.92/1.02  --res_prop_simpl_new                    false
% 0.92/1.02  --res_prop_simpl_given                  true
% 0.92/1.02  --res_passive_queue_type                priority_queues
% 0.92/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/1.02  --res_passive_queues_freq               [15;5]
% 0.92/1.02  --res_forward_subs                      full
% 0.92/1.02  --res_backward_subs                     full
% 0.92/1.02  --res_forward_subs_resolution           true
% 0.92/1.02  --res_backward_subs_resolution          true
% 0.92/1.02  --res_orphan_elimination                true
% 0.92/1.02  --res_time_limit                        2.
% 0.92/1.02  --res_out_proof                         true
% 0.92/1.02  
% 0.92/1.02  ------ Superposition Options
% 0.92/1.02  
% 0.92/1.02  --superposition_flag                    true
% 0.92/1.02  --sup_passive_queue_type                priority_queues
% 0.92/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.92/1.02  --demod_completeness_check              fast
% 0.92/1.02  --demod_use_ground                      true
% 0.92/1.02  --sup_to_prop_solver                    passive
% 0.92/1.02  --sup_prop_simpl_new                    true
% 0.92/1.02  --sup_prop_simpl_given                  true
% 0.92/1.02  --sup_fun_splitting                     false
% 0.92/1.02  --sup_smt_interval                      50000
% 0.92/1.02  
% 0.92/1.02  ------ Superposition Simplification Setup
% 0.92/1.02  
% 0.92/1.02  --sup_indices_passive                   []
% 0.92/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.02  --sup_full_bw                           [BwDemod]
% 0.92/1.02  --sup_immed_triv                        [TrivRules]
% 0.92/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.02  --sup_immed_bw_main                     []
% 0.92/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.02  
% 0.92/1.02  ------ Combination Options
% 0.92/1.02  
% 0.92/1.02  --comb_res_mult                         3
% 0.92/1.02  --comb_sup_mult                         2
% 0.92/1.02  --comb_inst_mult                        10
% 0.92/1.02  
% 0.92/1.02  ------ Debug Options
% 0.92/1.02  
% 0.92/1.02  --dbg_backtrace                         false
% 0.92/1.02  --dbg_dump_prop_clauses                 false
% 0.92/1.02  --dbg_dump_prop_clauses_file            -
% 0.92/1.02  --dbg_out_stat                          false
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  ------ Proving...
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  % SZS status Theorem for theBenchmark.p
% 0.92/1.02  
% 0.92/1.02   Resolution empty clause
% 0.92/1.02  
% 0.92/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.92/1.02  
% 0.92/1.02  fof(f2,axiom,(
% 0.92/1.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f15,plain,(
% 0.92/1.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.92/1.02    inference(ennf_transformation,[],[f2])).
% 0.92/1.02  
% 0.92/1.02  fof(f41,plain,(
% 0.92/1.02    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f15])).
% 0.92/1.02  
% 0.92/1.02  fof(f10,axiom,(
% 0.92/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f27,plain,(
% 0.92/1.02    ! [X0] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.92/1.02    inference(ennf_transformation,[],[f10])).
% 0.92/1.02  
% 0.92/1.02  fof(f28,plain,(
% 0.92/1.02    ! [X0] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.92/1.02    inference(flattening,[],[f27])).
% 0.92/1.02  
% 0.92/1.02  fof(f52,plain,(
% 0.92/1.02    ( ! [X0] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f28])).
% 0.92/1.02  
% 0.92/1.02  fof(f1,axiom,(
% 0.92/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f32,plain,(
% 0.92/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.92/1.02    inference(nnf_transformation,[],[f1])).
% 0.92/1.02  
% 0.92/1.02  fof(f40,plain,(
% 0.92/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f32])).
% 0.92/1.02  
% 0.92/1.02  fof(f11,axiom,(
% 0.92/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f29,plain,(
% 0.92/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.92/1.02    inference(ennf_transformation,[],[f11])).
% 0.92/1.02  
% 0.92/1.02  fof(f53,plain,(
% 0.92/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f29])).
% 0.92/1.02  
% 0.92/1.02  fof(f12,conjecture,(
% 0.92/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f13,negated_conjecture,(
% 0.92/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.92/1.02    inference(negated_conjecture,[],[f12])).
% 0.92/1.02  
% 0.92/1.02  fof(f30,plain,(
% 0.92/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.92/1.02    inference(ennf_transformation,[],[f13])).
% 0.92/1.02  
% 0.92/1.02  fof(f31,plain,(
% 0.92/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.92/1.02    inference(flattening,[],[f30])).
% 0.92/1.02  
% 0.92/1.02  fof(f37,plain,(
% 0.92/1.02    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) => (~m1_subset_1(k9_relat_1(k3_funct_3(X2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 0.92/1.02    introduced(choice_axiom,[])).
% 0.92/1.02  
% 0.92/1.02  fof(f36,plain,(
% 0.92/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(sK2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 0.92/1.02    introduced(choice_axiom,[])).
% 0.92/1.02  
% 0.92/1.02  fof(f35,plain,(
% 0.92/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 0.92/1.02    introduced(choice_axiom,[])).
% 0.92/1.02  
% 0.92/1.02  fof(f34,plain,(
% 0.92/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.92/1.02    introduced(choice_axiom,[])).
% 0.92/1.02  
% 0.92/1.02  fof(f38,plain,(
% 0.92/1.02    (((~m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.92/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f37,f36,f35,f34])).
% 0.92/1.02  
% 0.92/1.02  fof(f54,plain,(
% 0.92/1.02    l1_struct_0(sK0)),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  fof(f7,axiom,(
% 0.92/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f22,plain,(
% 0.92/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.92/1.02    inference(ennf_transformation,[],[f7])).
% 0.92/1.02  
% 0.92/1.02  fof(f48,plain,(
% 0.92/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f22])).
% 0.92/1.02  
% 0.92/1.02  fof(f59,plain,(
% 0.92/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  fof(f56,plain,(
% 0.92/1.02    l1_struct_0(sK1)),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  fof(f4,axiom,(
% 0.92/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f14,plain,(
% 0.92/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.92/1.02    inference(pure_predicate_removal,[],[f4])).
% 0.92/1.02  
% 0.92/1.02  fof(f17,plain,(
% 0.92/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/1.02    inference(ennf_transformation,[],[f14])).
% 0.92/1.02  
% 0.92/1.02  fof(f43,plain,(
% 0.92/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/1.02    inference(cnf_transformation,[],[f17])).
% 0.92/1.02  
% 0.92/1.02  fof(f6,axiom,(
% 0.92/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f20,plain,(
% 0.92/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.92/1.02    inference(ennf_transformation,[],[f6])).
% 0.92/1.02  
% 0.92/1.02  fof(f21,plain,(
% 0.92/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.92/1.02    inference(flattening,[],[f20])).
% 0.92/1.02  
% 0.92/1.02  fof(f33,plain,(
% 0.92/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.92/1.02    inference(nnf_transformation,[],[f21])).
% 0.92/1.02  
% 0.92/1.02  fof(f46,plain,(
% 0.92/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f33])).
% 0.92/1.02  
% 0.92/1.02  fof(f3,axiom,(
% 0.92/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f16,plain,(
% 0.92/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/1.02    inference(ennf_transformation,[],[f3])).
% 0.92/1.02  
% 0.92/1.02  fof(f42,plain,(
% 0.92/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/1.02    inference(cnf_transformation,[],[f16])).
% 0.92/1.02  
% 0.92/1.02  fof(f8,axiom,(
% 0.92/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f23,plain,(
% 0.92/1.02    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.92/1.02    inference(ennf_transformation,[],[f8])).
% 0.92/1.02  
% 0.92/1.02  fof(f24,plain,(
% 0.92/1.02    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.92/1.02    inference(flattening,[],[f23])).
% 0.92/1.02  
% 0.92/1.02  fof(f49,plain,(
% 0.92/1.02    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f24])).
% 0.92/1.02  
% 0.92/1.02  fof(f55,plain,(
% 0.92/1.02    ~v2_struct_0(sK1)),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  fof(f5,axiom,(
% 0.92/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f18,plain,(
% 0.92/1.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.92/1.02    inference(ennf_transformation,[],[f5])).
% 0.92/1.02  
% 0.92/1.02  fof(f19,plain,(
% 0.92/1.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.92/1.02    inference(flattening,[],[f18])).
% 0.92/1.02  
% 0.92/1.02  fof(f45,plain,(
% 0.92/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f19])).
% 0.92/1.02  
% 0.92/1.02  fof(f58,plain,(
% 0.92/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  fof(f57,plain,(
% 0.92/1.02    v1_funct_1(sK2)),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  fof(f39,plain,(
% 0.92/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.92/1.02    inference(cnf_transformation,[],[f32])).
% 0.92/1.02  
% 0.92/1.02  fof(f9,axiom,(
% 0.92/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k3_funct_3(X0)) & v1_relat_1(k3_funct_3(X0))))),
% 0.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.92/1.02  
% 0.92/1.02  fof(f25,plain,(
% 0.92/1.02    ! [X0] : ((v1_funct_1(k3_funct_3(X0)) & v1_relat_1(k3_funct_3(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.92/1.02    inference(ennf_transformation,[],[f9])).
% 0.92/1.02  
% 0.92/1.02  fof(f26,plain,(
% 0.92/1.02    ! [X0] : ((v1_funct_1(k3_funct_3(X0)) & v1_relat_1(k3_funct_3(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.92/1.02    inference(flattening,[],[f25])).
% 0.92/1.02  
% 0.92/1.02  fof(f50,plain,(
% 0.92/1.02    ( ! [X0] : (v1_relat_1(k3_funct_3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.92/1.02    inference(cnf_transformation,[],[f26])).
% 0.92/1.02  
% 0.92/1.02  fof(f61,plain,(
% 0.92/1.02    ~m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.92/1.02    inference(cnf_transformation,[],[f38])).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 0.92/1.02      inference(cnf_transformation,[],[f41]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_865,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(X0_50,X1_50),k2_relat_1(X0_50))
% 0.92/1.02      | ~ v1_relat_1(X0_50) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1268,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(X0_50,X1_50),k2_relat_1(X0_50)) = iProver_top
% 0.92/1.02      | v1_relat_1(X0_50) != iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_865]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_13,plain,
% 0.92/1.02      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
% 0.92/1.02      | ~ v1_funct_1(X0)
% 0.92/1.02      | ~ v1_relat_1(X0) ),
% 0.92/1.02      inference(cnf_transformation,[],[f52]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_861,plain,
% 0.92/1.02      ( r1_tarski(k2_relat_1(k3_funct_3(X0_50)),k1_zfmisc_1(k1_relat_1(X0_50)))
% 0.92/1.02      | ~ v1_funct_1(X0_50)
% 0.92/1.02      | ~ v1_relat_1(X0_50) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1272,plain,
% 0.92/1.02      ( r1_tarski(k2_relat_1(k3_funct_3(X0_50)),k1_zfmisc_1(k1_relat_1(X0_50))) = iProver_top
% 0.92/1.02      | v1_funct_1(X0_50) != iProver_top
% 0.92/1.02      | v1_relat_1(X0_50) != iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_0,plain,
% 0.92/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.92/1.02      inference(cnf_transformation,[],[f40]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_867,plain,
% 0.92/1.02      ( ~ r1_tarski(X0_50,X1_50) | m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1266,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_14,plain,
% 0.92/1.02      ( ~ r1_tarski(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 0.92/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 0.92/1.02      | ~ l1_struct_0(X2) ),
% 0.92/1.02      inference(cnf_transformation,[],[f53]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_22,negated_conjecture,
% 0.92/1.02      ( l1_struct_0(sK0) ),
% 0.92/1.02      inference(cnf_transformation,[],[f54]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_421,plain,
% 0.92/1.02      ( ~ r1_tarski(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 0.92/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 0.92/1.02      | sK0 != X2 ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_422,plain,
% 0.92/1.02      ( ~ r1_tarski(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.02      inference(unflattening,[status(thm)],[c_421]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_852,plain,
% 0.92/1.02      ( ~ r1_tarski(X0_50,X1_50)
% 0.92/1.02      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_422]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1279,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) != iProver_top
% 0.92/1.02      | m1_subset_1(X1_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_9,plain,
% 0.92/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.92/1.02      inference(cnf_transformation,[],[f48]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_403,plain,
% 0.92/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_404,plain,
% 0.92/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 0.92/1.02      inference(unflattening,[status(thm)],[c_403]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_854,plain,
% 0.92/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_404]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1342,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) != iProver_top
% 0.92/1.02      | m1_subset_1(X1_50,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) = iProver_top ),
% 0.92/1.02      inference(light_normalisation,[status(thm)],[c_1279,c_854]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1724,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) != iProver_top
% 0.92/1.02      | r1_tarski(X1_50,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) = iProver_top ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_1266,c_1342]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_17,negated_conjecture,
% 0.92/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 0.92/1.02      inference(cnf_transformation,[],[f59]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_858,negated_conjecture,
% 0.92/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1275,plain,
% 0.92/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_20,negated_conjecture,
% 0.92/1.02      ( l1_struct_0(sK1) ),
% 0.92/1.02      inference(cnf_transformation,[],[f56]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_398,plain,
% 0.92/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_399,plain,
% 0.92/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.92/1.02      inference(unflattening,[status(thm)],[c_398]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_855,plain,
% 0.92/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_399]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1289,plain,
% 0.92/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 0.92/1.02      inference(light_normalisation,[status(thm)],[c_1275,c_854,c_855]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_4,plain,
% 0.92/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.92/1.02      inference(cnf_transformation,[],[f43]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_8,plain,
% 0.92/1.02      ( ~ v1_partfun1(X0,X1)
% 0.92/1.02      | ~ v4_relat_1(X0,X1)
% 0.92/1.02      | ~ v1_relat_1(X0)
% 0.92/1.02      | k1_relat_1(X0) = X1 ),
% 0.92/1.02      inference(cnf_transformation,[],[f46]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_337,plain,
% 0.92/1.02      ( ~ v1_partfun1(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.02      | ~ v1_relat_1(X0)
% 0.92/1.02      | k1_relat_1(X0) = X1 ),
% 0.92/1.02      inference(resolution,[status(thm)],[c_4,c_8]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_3,plain,
% 0.92/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.92/1.02      inference(cnf_transformation,[],[f42]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_341,plain,
% 0.92/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.02      | ~ v1_partfun1(X0,X1)
% 0.92/1.02      | k1_relat_1(X0) = X1 ),
% 0.92/1.02      inference(global_propositional_subsumption,
% 0.92/1.02                [status(thm)],
% 0.92/1.02                [c_337,c_8,c_4,c_3]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_342,plain,
% 0.92/1.02      ( ~ v1_partfun1(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.02      | k1_relat_1(X0) = X1 ),
% 0.92/1.02      inference(renaming,[status(thm)],[c_341]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_10,plain,
% 0.92/1.02      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 0.92/1.02      inference(cnf_transformation,[],[f49]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_21,negated_conjecture,
% 0.92/1.02      ( ~ v2_struct_0(sK1) ),
% 0.92/1.02      inference(cnf_transformation,[],[f55]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_295,plain,
% 0.92/1.02      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_296,plain,
% 0.92/1.02      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.92/1.02      inference(unflattening,[status(thm)],[c_295]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_42,plain,
% 0.92/1.02      ( v2_struct_0(sK1)
% 0.92/1.02      | ~ l1_struct_0(sK1)
% 0.92/1.02      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.92/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_298,plain,
% 0.92/1.02      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.92/1.02      inference(global_propositional_subsumption,
% 0.92/1.02                [status(thm)],
% 0.92/1.02                [c_296,c_21,c_20,c_42]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_5,plain,
% 0.92/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 0.92/1.02      | v1_partfun1(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.02      | v1_xboole_0(X2)
% 0.92/1.02      | ~ v1_funct_1(X0) ),
% 0.92/1.02      inference(cnf_transformation,[],[f45]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_18,negated_conjecture,
% 0.92/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 0.92/1.02      inference(cnf_transformation,[],[f58]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_308,plain,
% 0.92/1.02      ( v1_partfun1(X0,X1)
% 0.92/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.02      | v1_xboole_0(X2)
% 0.92/1.02      | ~ v1_funct_1(X0)
% 0.92/1.02      | u1_struct_0(sK1) != X2
% 0.92/1.02      | u1_struct_0(sK0) != X1
% 0.92/1.02      | sK2 != X0 ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_309,plain,
% 0.92/1.02      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 0.92/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 0.92/1.02      | v1_xboole_0(u1_struct_0(sK1))
% 0.92/1.02      | ~ v1_funct_1(sK2) ),
% 0.92/1.02      inference(unflattening,[status(thm)],[c_308]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_19,negated_conjecture,
% 0.92/1.02      ( v1_funct_1(sK2) ),
% 0.92/1.02      inference(cnf_transformation,[],[f57]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_311,plain,
% 0.92/1.02      ( v1_xboole_0(u1_struct_0(sK1)) | v1_partfun1(sK2,u1_struct_0(sK0)) ),
% 0.92/1.02      inference(global_propositional_subsumption,
% 0.92/1.02                [status(thm)],
% 0.92/1.02                [c_309,c_19,c_17]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_312,plain,
% 0.92/1.02      ( v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) ),
% 0.92/1.02      inference(renaming,[status(thm)],[c_311]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_325,plain,
% 0.92/1.02      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 0.92/1.02      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_298,c_312]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_45,plain,
% 0.92/1.02      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.92/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_327,plain,
% 0.92/1.02      ( v1_partfun1(sK2,u1_struct_0(sK0)) ),
% 0.92/1.02      inference(global_propositional_subsumption,
% 0.92/1.02                [status(thm)],
% 0.92/1.02                [c_325,c_20,c_45]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_383,plain,
% 0.92/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.92/1.02      | u1_struct_0(sK0) != X1
% 0.92/1.02      | k1_relat_1(X0) = X1
% 0.92/1.02      | sK2 != X0 ),
% 0.92/1.02      inference(resolution_lifted,[status(thm)],[c_342,c_327]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_384,plain,
% 0.92/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 0.92/1.02      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.92/1.02      inference(unflattening,[status(thm)],[c_383]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_856,plain,
% 0.92/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50)))
% 0.92/1.02      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_384]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1277,plain,
% 0.92/1.02      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 0.92/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50))) != iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1311,plain,
% 0.92/1.02      ( u1_struct_0(sK0) = k1_relat_1(sK2)
% 0.92/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_50))) != iProver_top ),
% 0.92/1.02      inference(light_normalisation,[status(thm)],[c_1277,c_854]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1312,plain,
% 0.92/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 0.92/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_50))) != iProver_top ),
% 0.92/1.02      inference(demodulation,[status(thm)],[c_1311,c_854]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1476,plain,
% 0.92/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_1289,c_1312]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2118,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) != iProver_top
% 0.92/1.02      | r1_tarski(X1_50,k1_zfmisc_1(k1_relat_1(sK2))) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) = iProver_top ),
% 0.92/1.02      inference(light_normalisation,[status(thm)],[c_1724,c_1476]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2125,plain,
% 0.92/1.02      ( r1_tarski(X0_50,k2_relat_1(k3_funct_3(sK2))) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) = iProver_top
% 0.92/1.02      | v1_funct_1(sK2) != iProver_top
% 0.92/1.02      | v1_relat_1(sK2) != iProver_top ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_1272,c_2118]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_26,plain,
% 0.92/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_28,plain,
% 0.92/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_864,plain,
% 0.92/1.02      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 0.92/1.02      | v1_relat_1(X0_50) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1394,plain,
% 0.92/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 0.92/1.02      | v1_relat_1(sK2) ),
% 0.92/1.02      inference(instantiation,[status(thm)],[c_864]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1395,plain,
% 0.92/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 0.92/1.02      | v1_relat_1(sK2) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2490,plain,
% 0.92/1.02      ( r1_tarski(X0_50,k2_relat_1(k3_funct_3(sK2))) != iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) = iProver_top ),
% 0.92/1.02      inference(global_propositional_subsumption,
% 0.92/1.02                [status(thm)],
% 0.92/1.02                [c_2125,c_26,c_28,c_1395]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1,plain,
% 0.92/1.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.92/1.02      inference(cnf_transformation,[],[f39]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_866,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) | ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1267,plain,
% 0.92/1.02      ( r1_tarski(X0_50,X1_50) = iProver_top
% 0.92/1.02      | m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2498,plain,
% 0.92/1.02      ( r1_tarski(X0_50,k2_relat_1(k3_funct_3(sK2))) != iProver_top
% 0.92/1.02      | r1_tarski(X0_50,k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_2490,c_1267]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2521,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(k3_funct_3(sK2),X0_50),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top
% 0.92/1.02      | v1_relat_1(k3_funct_3(sK2)) != iProver_top ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_1268,c_2498]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_12,plain,
% 0.92/1.02      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k3_funct_3(X0)) ),
% 0.92/1.02      inference(cnf_transformation,[],[f50]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_862,plain,
% 0.92/1.02      ( ~ v1_funct_1(X0_50)
% 0.92/1.02      | ~ v1_relat_1(X0_50)
% 0.92/1.02      | v1_relat_1(k3_funct_3(X0_50)) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_908,plain,
% 0.92/1.02      ( v1_funct_1(X0_50) != iProver_top
% 0.92/1.02      | v1_relat_1(X0_50) != iProver_top
% 0.92/1.02      | v1_relat_1(k3_funct_3(X0_50)) = iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_910,plain,
% 0.92/1.02      ( v1_funct_1(sK2) != iProver_top
% 0.92/1.02      | v1_relat_1(k3_funct_3(sK2)) = iProver_top
% 0.92/1.02      | v1_relat_1(sK2) != iProver_top ),
% 0.92/1.02      inference(instantiation,[status(thm)],[c_908]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2562,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(k3_funct_3(sK2),X0_50),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 0.92/1.02      inference(global_propositional_subsumption,
% 0.92/1.02                [status(thm)],
% 0.92/1.02                [c_2521,c_26,c_28,c_910,c_1395]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_15,negated_conjecture,
% 0.92/1.02      ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.02      inference(cnf_transformation,[],[f61]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_860,negated_conjecture,
% 0.92/1.02      ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1273,plain,
% 0.92/1.02      ( m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 0.92/1.02      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1292,plain,
% 0.92/1.02      ( m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) != iProver_top ),
% 0.92/1.02      inference(light_normalisation,[status(thm)],[c_1273,c_854]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1558,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_1266,c_1292]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_1963,plain,
% 0.92/1.02      ( r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_relat_1(sK2))) != iProver_top ),
% 0.92/1.02      inference(light_normalisation,[status(thm)],[c_1558,c_1476]) ).
% 0.92/1.02  
% 0.92/1.02  cnf(c_2570,plain,
% 0.92/1.02      ( $false ),
% 0.92/1.02      inference(superposition,[status(thm)],[c_2562,c_1963]) ).
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.92/1.02  
% 0.92/1.02  ------                               Statistics
% 0.92/1.02  
% 0.92/1.02  ------ General
% 0.92/1.02  
% 0.92/1.02  abstr_ref_over_cycles:                  0
% 0.92/1.02  abstr_ref_under_cycles:                 0
% 0.92/1.02  gc_basic_clause_elim:                   0
% 0.92/1.02  forced_gc_time:                         0
% 0.92/1.02  parsing_time:                           0.01
% 0.92/1.02  unif_index_cands_time:                  0.
% 0.92/1.02  unif_index_add_time:                    0.
% 0.92/1.02  orderings_time:                         0.
% 0.92/1.02  out_proof_time:                         0.012
% 0.92/1.02  total_time:                             0.117
% 0.92/1.02  num_of_symbols:                         55
% 0.92/1.02  num_of_terms:                           2226
% 0.92/1.02  
% 0.92/1.02  ------ Preprocessing
% 0.92/1.02  
% 0.92/1.02  num_of_splits:                          0
% 0.92/1.02  num_of_split_atoms:                     0
% 0.92/1.02  num_of_reused_defs:                     0
% 0.92/1.02  num_eq_ax_congr_red:                    6
% 0.92/1.02  num_of_sem_filtered_clauses:            1
% 0.92/1.02  num_of_subtypes:                        2
% 0.92/1.02  monotx_restored_types:                  0
% 0.92/1.02  sat_num_of_epr_types:                   0
% 0.92/1.02  sat_num_of_non_cyclic_types:            0
% 0.92/1.02  sat_guarded_non_collapsed_types:        0
% 0.92/1.02  num_pure_diseq_elim:                    0
% 0.92/1.02  simp_replaced_by:                       0
% 0.92/1.02  res_preprocessed:                       95
% 0.92/1.02  prep_upred:                             0
% 0.92/1.02  prep_unflattend:                        38
% 0.92/1.02  smt_new_axioms:                         0
% 0.92/1.02  pred_elim_cands:                        4
% 0.92/1.02  pred_elim:                              6
% 0.92/1.02  pred_elim_cl:                           6
% 0.92/1.02  pred_elim_cycles:                       8
% 0.92/1.02  merged_defs:                            8
% 0.92/1.02  merged_defs_ncl:                        0
% 0.92/1.02  bin_hyper_res:                          8
% 0.92/1.02  prep_cycles:                            4
% 0.92/1.02  pred_elim_time:                         0.007
% 0.92/1.02  splitting_time:                         0.
% 0.92/1.02  sem_filter_time:                        0.
% 0.92/1.02  monotx_time:                            0.
% 0.92/1.02  subtype_inf_time:                       0.
% 0.92/1.02  
% 0.92/1.02  ------ Problem properties
% 0.92/1.02  
% 0.92/1.02  clauses:                                16
% 0.92/1.02  conjectures:                            4
% 0.92/1.02  epr:                                    1
% 0.92/1.02  horn:                                   16
% 0.92/1.02  ground:                                 6
% 0.92/1.02  unary:                                  6
% 0.92/1.02  binary:                                 5
% 0.92/1.02  lits:                                   31
% 0.92/1.02  lits_eq:                                3
% 0.92/1.02  fd_pure:                                0
% 0.92/1.02  fd_pseudo:                              0
% 0.92/1.02  fd_cond:                                0
% 0.92/1.02  fd_pseudo_cond:                         0
% 0.92/1.02  ac_symbols:                             0
% 0.92/1.02  
% 0.92/1.02  ------ Propositional Solver
% 0.92/1.02  
% 0.92/1.02  prop_solver_calls:                      28
% 0.92/1.02  prop_fast_solver_calls:                 576
% 0.92/1.02  smt_solver_calls:                       0
% 0.92/1.02  smt_fast_solver_calls:                  0
% 0.92/1.02  prop_num_of_clauses:                    731
% 0.92/1.02  prop_preprocess_simplified:             3107
% 0.92/1.02  prop_fo_subsumed:                       8
% 0.92/1.02  prop_solver_time:                       0.
% 0.92/1.02  smt_solver_time:                        0.
% 0.92/1.02  smt_fast_solver_time:                   0.
% 0.92/1.02  prop_fast_solver_time:                  0.
% 0.92/1.02  prop_unsat_core_time:                   0.
% 0.92/1.02  
% 0.92/1.02  ------ QBF
% 0.92/1.02  
% 0.92/1.02  qbf_q_res:                              0
% 0.92/1.02  qbf_num_tautologies:                    0
% 0.92/1.02  qbf_prep_cycles:                        0
% 0.92/1.02  
% 0.92/1.02  ------ BMC1
% 0.92/1.02  
% 0.92/1.02  bmc1_current_bound:                     -1
% 0.92/1.02  bmc1_last_solved_bound:                 -1
% 0.92/1.02  bmc1_unsat_core_size:                   -1
% 0.92/1.02  bmc1_unsat_core_parents_size:           -1
% 0.92/1.02  bmc1_merge_next_fun:                    0
% 0.92/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.92/1.02  
% 0.92/1.02  ------ Instantiation
% 0.92/1.02  
% 0.92/1.02  inst_num_of_clauses:                    233
% 0.92/1.02  inst_num_in_passive:                    29
% 0.92/1.02  inst_num_in_active:                     178
% 0.92/1.02  inst_num_in_unprocessed:                27
% 0.92/1.02  inst_num_of_loops:                      190
% 0.92/1.02  inst_num_of_learning_restarts:          0
% 0.92/1.02  inst_num_moves_active_passive:          7
% 0.92/1.02  inst_lit_activity:                      0
% 0.92/1.02  inst_lit_activity_moves:                0
% 0.92/1.02  inst_num_tautologies:                   0
% 0.92/1.02  inst_num_prop_implied:                  0
% 0.92/1.02  inst_num_existing_simplified:           0
% 0.92/1.02  inst_num_eq_res_simplified:             0
% 0.92/1.02  inst_num_child_elim:                    0
% 0.92/1.02  inst_num_of_dismatching_blockings:      42
% 0.92/1.02  inst_num_of_non_proper_insts:           259
% 0.92/1.02  inst_num_of_duplicates:                 0
% 0.92/1.02  inst_inst_num_from_inst_to_res:         0
% 0.92/1.02  inst_dismatching_checking_time:         0.
% 0.92/1.02  
% 0.92/1.02  ------ Resolution
% 0.92/1.02  
% 0.92/1.02  res_num_of_clauses:                     0
% 0.92/1.02  res_num_in_passive:                     0
% 0.92/1.02  res_num_in_active:                      0
% 0.92/1.02  res_num_of_loops:                       99
% 0.92/1.02  res_forward_subset_subsumed:            53
% 0.92/1.02  res_backward_subset_subsumed:           2
% 0.92/1.02  res_forward_subsumed:                   0
% 0.92/1.02  res_backward_subsumed:                  0
% 0.92/1.02  res_forward_subsumption_resolution:     1
% 0.92/1.02  res_backward_subsumption_resolution:    0
% 0.92/1.02  res_clause_to_clause_subsumption:       156
% 0.92/1.02  res_orphan_elimination:                 0
% 0.92/1.02  res_tautology_del:                      90
% 0.92/1.02  res_num_eq_res_simplified:              0
% 0.92/1.02  res_num_sel_changes:                    0
% 0.92/1.02  res_moves_from_active_to_pass:          0
% 0.92/1.02  
% 0.92/1.02  ------ Superposition
% 0.92/1.02  
% 0.92/1.02  sup_time_total:                         0.
% 0.92/1.02  sup_time_generating:                    0.
% 0.92/1.02  sup_time_sim_full:                      0.
% 0.92/1.02  sup_time_sim_immed:                     0.
% 0.92/1.02  
% 0.92/1.02  sup_num_of_clauses:                     36
% 0.92/1.02  sup_num_in_active:                      32
% 0.92/1.02  sup_num_in_passive:                     4
% 0.92/1.02  sup_num_of_loops:                       36
% 0.92/1.02  sup_fw_superposition:                   18
% 0.92/1.02  sup_bw_superposition:                   14
% 0.92/1.02  sup_immediate_simplified:               3
% 0.92/1.02  sup_given_eliminated:                   0
% 0.92/1.02  comparisons_done:                       0
% 0.92/1.02  comparisons_avoided:                    0
% 0.92/1.02  
% 0.92/1.02  ------ Simplifications
% 0.92/1.02  
% 0.92/1.02  
% 0.92/1.02  sim_fw_subset_subsumed:                 1
% 0.92/1.02  sim_bw_subset_subsumed:                 2
% 0.92/1.02  sim_fw_subsumed:                        1
% 0.92/1.02  sim_bw_subsumed:                        0
% 0.92/1.02  sim_fw_subsumption_res:                 0
% 0.92/1.02  sim_bw_subsumption_res:                 0
% 0.92/1.02  sim_tautology_del:                      1
% 0.92/1.02  sim_eq_tautology_del:                   0
% 0.92/1.02  sim_eq_res_simp:                        0
% 0.92/1.02  sim_fw_demodulated:                     1
% 0.92/1.02  sim_bw_demodulated:                     4
% 0.92/1.02  sim_light_normalised:                   9
% 0.92/1.02  sim_joinable_taut:                      0
% 0.92/1.02  sim_joinable_simp:                      0
% 0.92/1.02  sim_ac_normalised:                      0
% 0.92/1.02  sim_smt_subsumption:                    0
% 0.92/1.02  
%------------------------------------------------------------------------------
