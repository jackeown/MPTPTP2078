%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1135+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:47 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 131 expanded)
%              Number of clauses        :   32 (  54 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 489 expanded)
%              Number of equality atoms :   30 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

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

fof(t66_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
             => ( X2 = X3
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ( X7 != k1_pre_topc(X5,X6)
        | k2_struct_0(X7) = X6
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( k2_struct_0(X7) != X6
        | X7 = k1_pre_topc(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ( v1_pre_topc(k1_pre_topc(X10,X11))
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) )
      & ( m1_pre_topc(k1_pre_topc(X10,X11),X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ( v1_pre_topc(g1_pre_topc(X8,X9))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) )
      & ( l1_pre_topc(g1_pre_topc(X8,X9))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_11,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
               => ( X2 = X3
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_pre_topc])).

cnf(c_0_13,plain,
    ( X1 = k1_pre_topc(X3,X2)
    | k2_struct_0(X1) != X2
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ( ~ m1_pre_topc(X15,X16)
        | m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | m1_pre_topc(X15,X16)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

cnf(c_0_18,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    & esk2_0 = esk3_0
    & g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_21,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | l1_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_22,plain,
    ( k1_pre_topc(X1,k2_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | ~ v1_pre_topc(X4)
      | X4 = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k1_pre_topc(X1,X2) = k1_pre_topc(X3,X2)
    | ~ m1_pre_topc(k1_pre_topc(X3,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])).

cnf(c_0_31,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = k1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) != k1_pre_topc(esk1_0,esk2_0)
    | ~ v1_pre_topc(k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) = k1_pre_topc(esk1_0,esk2_0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) != k1_pre_topc(esk1_0,esk2_0)
    | ~ v1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) = k1_pre_topc(esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_pre_topc(k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_25]),c_0_37])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_15]),c_0_36]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
