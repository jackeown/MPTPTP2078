%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1798+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 35.47s
% Output     : CNFRefutation 35.47s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 193 expanded)
%              Number of clauses        :   20 (  64 expanded)
%              Number of leaves         :    5 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  180 (1438 expanded)
%              Number of equality atoms :   40 ( 390 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X3 = u1_struct_0(X2)
                   => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t114_tmap_1])).

fof(c_0_6,plain,(
    ! [X10611,X10612,X10613,X10614] :
      ( ( X10613 != k8_tmap_1(X10611,X10612)
        | ~ m1_subset_1(X10614,k1_zfmisc_1(u1_struct_0(X10611)))
        | X10614 != u1_struct_0(X10612)
        | X10613 = k6_tmap_1(X10611,X10614)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) )
      & ( m1_subset_1(esk1254_3(X10611,X10612,X10613),k1_zfmisc_1(u1_struct_0(X10611)))
        | X10613 = k8_tmap_1(X10611,X10612)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) )
      & ( esk1254_3(X10611,X10612,X10613) = u1_struct_0(X10612)
        | X10613 = k8_tmap_1(X10611,X10612)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) )
      & ( X10613 != k6_tmap_1(X10611,esk1254_3(X10611,X10612,X10613))
        | X10613 = k8_tmap_1(X10611,X10612)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_7,plain,(
    ! [X10838,X10839] :
      ( ~ l1_pre_topc(X10838)
      | ~ m1_pre_topc(X10839,X10838)
      | m1_subset_1(u1_struct_0(X10839),k1_zfmisc_1(u1_struct_0(X10838))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_8,plain,(
    ! [X10696,X10697] :
      ( ( v1_pre_topc(k8_tmap_1(X10696,X10697))
        | v2_struct_0(X10696)
        | ~ v2_pre_topc(X10696)
        | ~ l1_pre_topc(X10696)
        | ~ m1_pre_topc(X10697,X10696) )
      & ( v2_pre_topc(k8_tmap_1(X10696,X10697))
        | v2_struct_0(X10696)
        | ~ v2_pre_topc(X10696)
        | ~ l1_pre_topc(X10696)
        | ~ m1_pre_topc(X10697,X10696) )
      & ( l1_pre_topc(k8_tmap_1(X10696,X10697))
        | v2_struct_0(X10696)
        | ~ v2_pre_topc(X10696)
        | ~ l1_pre_topc(X10696)
        | ~ m1_pre_topc(X10697,X10696) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1267_0)
    & v2_pre_topc(esk1267_0)
    & l1_pre_topc(esk1267_0)
    & ~ v2_struct_0(esk1268_0)
    & m1_pre_topc(esk1268_0,esk1267_0)
    & ( m1_subset_1(esk1269_0,k1_zfmisc_1(u1_struct_0(esk1267_0)))
      | u1_struct_0(k8_tmap_1(esk1267_0,esk1268_0)) != u1_struct_0(esk1267_0) )
    & ( esk1269_0 = u1_struct_0(esk1268_0)
      | u1_struct_0(k8_tmap_1(esk1267_0,esk1268_0)) != u1_struct_0(esk1267_0) )
    & ( u1_pre_topc(k8_tmap_1(esk1267_0,esk1268_0)) != k5_tmap_1(esk1267_0,esk1269_0)
      | u1_struct_0(k8_tmap_1(esk1267_0,esk1268_0)) != u1_struct_0(esk1267_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

cnf(c_0_10,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X10755,X10756] :
      ( ( u1_struct_0(k6_tmap_1(X10755,X10756)) = u1_struct_0(X10755)
        | ~ m1_subset_1(X10756,k1_zfmisc_1(u1_struct_0(X10755)))
        | v2_struct_0(X10755)
        | ~ v2_pre_topc(X10755)
        | ~ l1_pre_topc(X10755) )
      & ( u1_pre_topc(k6_tmap_1(X10755,X10756)) = k5_tmap_1(X10755,X10756)
        | ~ m1_subset_1(X10756,k1_zfmisc_1(u1_struct_0(X10755)))
        | v2_struct_0(X10755)
        | ~ v2_pre_topc(X10755)
        | ~ l1_pre_topc(X10755) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk1268_0,esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])]),c_0_11]),c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1268_0),k1_zfmisc_1(u1_struct_0(esk1267_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( esk1269_0 = u1_struct_0(esk1268_0)
    | u1_struct_0(k8_tmap_1(esk1267_0,esk1268_0)) != u1_struct_0(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k8_tmap_1(esk1267_0,esk1268_0) = k6_tmap_1(esk1267_0,u1_struct_0(esk1268_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk1267_0,u1_struct_0(esk1268_0))) = u1_struct_0(esk1267_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk1267_0,esk1268_0)) != k5_tmap_1(esk1267_0,esk1269_0)
    | u1_struct_0(k8_tmap_1(esk1267_0,esk1268_0)) != u1_struct_0(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1267_0,u1_struct_0(esk1268_0))) = k5_tmap_1(esk1267_0,u1_struct_0(esk1268_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk1268_0) = esk1269_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_25]),c_0_28]),c_0_25]),c_0_26])]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
