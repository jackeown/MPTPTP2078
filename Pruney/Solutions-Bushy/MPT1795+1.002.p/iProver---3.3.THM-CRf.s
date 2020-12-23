%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1795+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 412 expanded)
%              Number of clauses        :   67 (  96 expanded)
%              Number of leaves         :   14 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          :  784 (3783 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
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
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

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
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f77,plain,(
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

fof(f86,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
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

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f75,plain,(
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

fof(f85,plain,(
    r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1599,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0),u1_struct_0(X1))
    | m1_subset_1(k2_tmap_1(X0,X1,k7_tmap_1(sK1,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1882,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_3021,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1598,plain,
    ( v1_funct_2(k2_tmap_1(X0,X1,k7_tmap_1(sK1,sK2),X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1877,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),X0),u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_2277,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1266,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k6_tmap_1(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2094,plain,
    ( v2_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1270])).

cnf(c_2095,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2094])).

cnf(c_14,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2084,plain,
    ( l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1600,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v1_funct_1(k2_tmap_1(X0,X1,k7_tmap_1(sK1,sK2),X2))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1872,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),X0))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1600])).

cnf(c_2070,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k6_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_460,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_461,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_463,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_31])).

cnf(c_1262,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1272,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1713,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1272])).

cnf(c_1719,plain,
    ( l1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1713])).

cnf(c_12,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1584,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1581,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1550,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1540,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_24,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_529,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3) != X0
    | k6_tmap_1(sK1,sK2) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_530,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_471,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_472,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_23,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK0(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_396,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_397,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,sK2),k2_tmap_1(X1,k6_tmap_1(X1,sK2),k7_tmap_1(X1,sK2),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_439,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,sK2),k2_tmap_1(X1,k6_tmap_1(X1,sK2),k7_tmap_1(X1,sK2),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_397,c_28])).

cnf(c_440,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_33,c_32,c_31,c_30,c_29])).

cnf(c_445,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_492,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3) != X0
    | sK0(X2,X1,X0) != X3
    | k6_tmap_1(sK1,sK2) != X2
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_445])).

cnf(c_493,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK3,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_32,c_31,c_29,c_26,c_461,c_472])).

cnf(c_496,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k6_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_532,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_32,c_31,c_29,c_461,c_472,c_496])).

cnf(c_533,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3))
    | v2_struct_0(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_72,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3021,c_2277,c_2095,c_2084,c_2070,c_1719,c_1584,c_1581,c_1550,c_1543,c_1540,c_533,c_72,c_30,c_31,c_32,c_33])).


%------------------------------------------------------------------------------
