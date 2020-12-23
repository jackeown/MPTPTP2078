%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1795+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 415 expanded)
%              Number of clauses        :   76 ( 105 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  839 (3735 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
             => ( r1_xboole_0(u1_struct_0(X2),X1)
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
               => ( r1_xboole_0(u1_struct_0(X2),X1)
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
              & r1_xboole_0(u1_struct_0(X2),X1)
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
              & r1_xboole_0(u1_struct_0(X2),X1)
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
          & r1_xboole_0(u1_struct_0(X2),X1)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),sK3,k6_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3)) )
        & r1_xboole_0(u1_struct_0(sK3),X1)
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
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK2)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),X2,k6_tmap_1(X0,sK2))
              | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK2)))
              | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2)) )
            & r1_xboole_0(u1_struct_0(X2),sK2)
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
                & r1_xboole_0(u1_struct_0(X2),X1)
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
              & r1_xboole_0(u1_struct_0(X2),X1)
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
    & r1_xboole_0(u1_struct_0(sK3),sK2)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f51,f50,f49])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
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

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
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

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f79,plain,(
    v2_pre_topc(sK1) ),
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
             => ( r1_xboole_0(u1_struct_0(X2),X1)
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
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
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
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
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
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_661,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_53,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1432,plain,
    ( ~ v1_funct_2(k7_tmap_1(X0_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X2_55))
    | m1_subset_1(k2_tmap_1(X1_55,X2_55,k7_tmap_1(X0_55,X0_53),X3_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X2_55))))
    | ~ m1_subset_1(k7_tmap_1(X0_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X2_55))))
    | ~ v1_funct_1(k7_tmap_1(X0_55,X0_53))
    | ~ l1_struct_0(X3_55)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X1_55) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_1541,plain,
    ( ~ v1_funct_2(k7_tmap_1(X0_55,X0_53),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))
    | m1_subset_1(k2_tmap_1(X0_55,k6_tmap_1(X0_55,X0_53),k7_tmap_1(X0_55,X0_53),X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))))
    | ~ m1_subset_1(k7_tmap_1(X0_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))))
    | ~ v1_funct_1(k7_tmap_1(X0_55,X0_53))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55)
    | ~ l1_struct_0(k6_tmap_1(X0_55,X0_53)) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_2394,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_660,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k2_tmap_1(X0_55,X1_55,X0_53,X2_55),u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1427,plain,
    ( v1_funct_2(k2_tmap_1(X0_55,X1_55,k7_tmap_1(X2_55,X0_53),X3_55),u1_struct_0(X3_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(k7_tmap_1(X2_55,X0_53),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(k7_tmap_1(X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(k7_tmap_1(X2_55,X0_53))
    | ~ l1_struct_0(X3_55)
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1536,plain,
    ( v1_funct_2(k2_tmap_1(X0_55,k6_tmap_1(X0_55,X0_53),k7_tmap_1(X0_55,X0_53),X1_55),u1_struct_0(X1_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))
    | ~ v1_funct_2(k7_tmap_1(X0_55,X0_53),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))
    | ~ m1_subset_1(k7_tmap_1(X0_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))))
    | ~ v1_funct_1(k7_tmap_1(X0_55,X0_53))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55)
    | ~ l1_struct_0(k6_tmap_1(X0_55,X0_53)) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_2137,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_659,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tmap_1(X0_55,X1_55,X0_53,X2_55))
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1422,plain,
    ( ~ v1_funct_2(k7_tmap_1(X0_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X2_55))
    | ~ m1_subset_1(k7_tmap_1(X0_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X2_55))))
    | v1_funct_1(k2_tmap_1(X1_55,X2_55,k7_tmap_1(X0_55,X0_53),X3_55))
    | ~ v1_funct_1(k7_tmap_1(X0_55,X0_53))
    | ~ l1_struct_0(X3_55)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X1_55) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_1531,plain,
    ( ~ v1_funct_2(k7_tmap_1(X0_55,X0_53),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))
    | ~ m1_subset_1(k7_tmap_1(X0_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))))
    | v1_funct_1(k2_tmap_1(X0_55,k6_tmap_1(X0_55,X0_53),k7_tmap_1(X0_55,X0_53),X1_55))
    | ~ v1_funct_1(k7_tmap_1(X0_55,X0_53))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55)
    | ~ l1_struct_0(k6_tmap_1(X0_55,X0_53)) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_1872,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_652,plain,
    ( l1_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1730,plain,
    ( l1_struct_0(k6_tmap_1(X0_55,X0_53))
    | ~ l1_pre_topc(k6_tmap_1(X0_55,X0_53)) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_1732,plain,
    ( l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_386,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_387,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_389,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_28])).

cnf(c_643,plain,
    ( l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1149,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_1141,plain,
    ( l1_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1603,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1141])).

cnf(c_1609,plain,
    ( l1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1603])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_55)))
    | v2_struct_0(X0_55)
    | ~ v2_struct_0(k6_tmap_1(X0_55,X0_53))
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_740,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k6_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_55)))
    | v1_funct_1(k7_tmap_1(X0_55,X0_53))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_10,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_655,plain,
    ( v1_funct_2(k7_tmap_1(X0_55,X0_53),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_55)))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_730,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_55)))
    | m1_subset_1(k7_tmap_1(X0_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(X0_55,X0_53)))))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_727,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_55)))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55)
    | v2_pre_topc(k6_tmap_1(X0_55,X0_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_724,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_55)))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(k6_tmap_1(X0_55,X0_53))
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_658])).

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

cnf(c_455,plain,
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

cnf(c_456,plain,
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
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_397,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_398,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_397])).

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
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_322,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_323,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,sK2),k2_tmap_1(X1,k6_tmap_1(X1,sK2),k7_tmap_1(X1,sK2),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_365,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,sK2),k2_tmap_1(X1,k6_tmap_1(X1,sK2),k7_tmap_1(X1,sK2),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_323,c_25])).

cnf(c_366,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_30,c_29,c_28,c_27,c_26])).

cnf(c_371,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_418,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3) != X0
    | sK0(X2,X1,X0) != X3
    | k6_tmap_1(sK1,sK2) != X2
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_371])).

cnf(c_419,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_421,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_29,c_28,c_26,c_23,c_387,c_398])).

cnf(c_422,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_458,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_29,c_28,c_26,c_387,c_398,c_422])).

cnf(c_459,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_63,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2394,c_2137,c_1872,c_1732,c_1609,c_740,c_733,c_730,c_727,c_724,c_721,c_459,c_63,c_27,c_28,c_29,c_30])).


%------------------------------------------------------------------------------
