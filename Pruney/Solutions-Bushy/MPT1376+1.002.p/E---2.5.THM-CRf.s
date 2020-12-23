%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1376+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 584 expanded)
%              Number of clauses        :   44 ( 231 expanded)
%              Number of leaves         :    8 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 (2903 expanded)
%              Number of equality atoms :   13 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t32_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tops_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        <=> ( v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_tops_2(X7,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X8,X7)
        | v3_pre_topc(X8,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | v1_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | v1_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( ~ v3_pre_topc(esk1_2(X6,X7),X6)
        | v1_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_tops_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          <=> ( v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_compts_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | g1_pre_topc(X13,X14) != g1_pre_topc(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( X14 = X16
        | g1_pre_topc(X13,X14) != g1_pre_topc(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_12,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ( v1_pre_topc(g1_pre_topc(X10,X11))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( l1_pre_topc(g1_pre_topc(X10,X11))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_14,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ( ~ v1_tops_2(esk3_0,esk2_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
      | ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) )
    & ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
      | v1_tops_2(esk3_0,esk2_0) )
    & ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
      | v1_tops_2(esk3_0,esk2_0) )
    & ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])]),c_0_19]),c_0_20])).

fof(c_0_26,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_27,negated_conjecture,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v1_tops_2(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v1_tops_2(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ( v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))
        | ~ v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( v3_pre_topc(X23,X22)
        | ~ v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

cnf(c_0_35,negated_conjecture,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v1_tops_2(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v3_pre_topc(esk1_2(esk2_0,esk3_0),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0)
    | m1_subset_1(esk1_2(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_42,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)
    | v1_tops_2(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_30])]),c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(g1_pre_topc(X1,X2),X3),X3)
    | v1_tops_2(X3,g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ v1_tops_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_33]),c_0_30])])).

cnf(c_0_46,negated_conjecture,
    ( v1_tops_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_33]),c_0_30])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),X1),esk3_0),esk3_0)
    | v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),esk3_0)
    | v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_29]),c_0_30])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_tops_2(esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_33])])).

cnf(c_0_54,plain,
    ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v3_pre_topc(esk1_2(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1),X2)
    | ~ m1_subset_1(esk1_2(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),esk2_0)
    | v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | m1_subset_1(esk1_2(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_46])])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_40]),c_0_30])]),c_0_56]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_25]),c_0_33])]),c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
