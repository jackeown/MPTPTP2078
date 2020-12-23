%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1796+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:26 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  182 (1126 expanded)
%              Number of clauses        :  112 ( 321 expanded)
%              Number of leaves         :   16 ( 324 expanded)
%              Depth                    :   26
%              Number of atoms          : 1060 (9444 expanded)
%              Number of equality atoms :  287 (1269 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( u1_struct_0(X2) = X1
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
          & u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),sK3,k6_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3)) )
        & u1_struct_0(sK3) = X1
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK2)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),X2,k6_tmap_1(X0,sK2))
              | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK2)))
              | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2)) )
            & u1_struct_0(X2) = sK2
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
                & u1_struct_0(X2) = X1
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK1,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),X2,k6_tmap_1(sK1,X1))
                | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK1,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) )
    & u1_struct_0(sK3) = sK2
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f51,f50,f49])).

fof(f84,plain,(
    u1_struct_0(sK3) = sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_relat_1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_24,negated_conjecture,
    ( u1_struct_0(sK3) = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_664,negated_conjecture,
    ( u1_struct_0(sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_676,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_52,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1142,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_52,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X2_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_3017,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_52,sK3),sK2,u1_struct_0(X1_53)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_1142])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_334,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_335,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_336,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_668,plain,
    ( l1_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1232,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_1233,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_3407,plain,
    ( l1_struct_0(X1_53) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_52,sK3),sK2,u1_struct_0(X1_53)) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3017,c_33,c_336,c_1233])).

cnf(c_3408,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_52,sK3),sK2,u1_struct_0(X1_53)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3407])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_677,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_52,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1141,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_52,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X2_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_2277,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(X1_53)))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_1141])).

cnf(c_2676,plain,
    ( l1_struct_0(X1_53) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(X1_53)))) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2277,c_33,c_336,c_1233])).

cnf(c_2677,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(X1_53)))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2676])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_662,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1154,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_relat_1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53)
    | k7_tmap_1(X0_53,X0_52) = k6_relat_1(u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1140,plain,
    ( k7_tmap_1(X0_53,X0_52) = k6_relat_1(u1_struct_0(X0_53))
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1736,plain,
    ( k6_relat_1(u1_struct_0(sK1)) = k7_tmap_1(sK1,sK2)
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1140])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_32,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2145,plain,
    ( k6_relat_1(u1_struct_0(sK1)) = k7_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1736,c_31,c_32,c_33])).

cnf(c_21,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_411,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3) != X0
    | k6_tmap_1(sK1,sK2) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_412,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_345,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_346,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_414,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_29,c_28,c_26,c_335,c_346])).

cnf(c_415,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_656,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_415])).

cnf(c_1160,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_1162,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),sK2) = iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1160,c_664])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_61,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_63,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(k6_tmap_1(X0_53,X0_52))
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_735,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_53,X0_52)) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53)
    | v2_pre_topc(k6_tmap_1(X0_53,X0_52)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_738,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_53,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_740,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | m1_subset_1(k7_tmap_1(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(k6_tmap_1(X0_53,X0_52)))))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_741,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(k6_tmap_1(X0_53,X0_52))))) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_743,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_10,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_671,plain,
    ( v1_funct_2(k7_tmap_1(X0_53,X0_52),u1_struct_0(X0_53),u1_struct_0(k6_tmap_1(X0_53,X0_52)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_744,plain,
    ( v1_funct_2(k7_tmap_1(X0_53,X0_52),u1_struct_0(X0_53),u1_struct_0(k6_tmap_1(X0_53,X0_52))) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_746,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v1_funct_1(k7_tmap_1(X0_53,X0_52))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_747,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_53,X0_52)) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_749,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v2_struct_0(X0_53)
    | ~ v2_struct_0(k6_tmap_1(X0_53,X0_52))
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_754,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(k6_tmap_1(X0_53,X0_52)) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_756,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK0(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_313,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_314,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,u1_struct_0(sK3)),k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_318,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,u1_struct_0(sK3)),k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_30,c_29,c_28,c_26])).

cnf(c_366,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != X0
    | sK0(X2,X1,X0) != X3
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_318])).

cnf(c_367,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),sK3,k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3))
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_369,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))
    | v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),sK3,k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_29,c_28,c_26,c_335,c_346])).

cnf(c_370,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),sK3,k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3))
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_440,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k6_tmap_1(sK1,sK2)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_370])).

cnf(c_517,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k6_tmap_1(sK1,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_440])).

cnf(c_655,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3)))
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k6_tmap_1(sK1,sK2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_517])).

cnf(c_1161,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) != k6_tmap_1(sK1,sK2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)
    | v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,u1_struct_0(sK3)),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK3)),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_1163,plain,
    ( k6_tmap_1(sK1,sK2) != k6_tmap_1(sK1,sK2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3) != k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)
    | v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1161,c_664])).

cnf(c_1164,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1163])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_675,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_52,X2_53))
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1211,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1212,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_1258,plain,
    ( l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_1259,plain,
    ( l1_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_1346,plain,
    ( m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1162,c_31,c_32,c_33,c_34,c_63,c_336,c_737,c_740,c_743,c_746,c_749,c_756,c_1164,c_1212,c_1233,c_1259])).

cnf(c_1347,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1346])).

cnf(c_2147,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k6_relat_1(u1_struct_0(sK1)),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k6_relat_1(u1_struct_0(sK1)),sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2145,c_1347])).

cnf(c_2685,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k6_relat_1(u1_struct_0(sK1)),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_2(k6_relat_1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k6_relat_1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k6_relat_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2147])).

cnf(c_1148,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_53,X0_52)) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_2465,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1148])).

cnf(c_2470,plain,
    ( v1_funct_1(k6_relat_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2465,c_2145])).

cnf(c_1147,plain,
    ( v1_funct_2(k7_tmap_1(X0_53,X0_52),u1_struct_0(X0_53),u1_struct_0(k6_tmap_1(X0_53,X0_52))) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_3232,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_1147])).

cnf(c_1146,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(k6_tmap_1(X0_53,X0_52))))) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_3919,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_1146])).

cnf(c_5259,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k6_relat_1(u1_struct_0(sK1)),sK3),sK2,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_31,c_32,c_33,c_34,c_63,c_737,c_1259,c_2470,c_3232,c_3919])).

cnf(c_5263,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k6_relat_1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k6_relat_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_5259])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5263,c_3919,c_3232,c_2470,c_1259,c_737,c_63,c_34,c_33,c_32,c_31])).


%------------------------------------------------------------------------------
