%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:55 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  135 (1307 expanded)
%              Number of clauses        :   97 ( 550 expanded)
%              Number of leaves         :   19 ( 348 expanded)
%              Depth                    :   13
%              Number of atoms          :  332 (3571 expanded)
%              Number of equality atoms :   85 (1223 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t4_waybel_7,axiom,(
    ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t15_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t14_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(t2_yellow19,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,plain,(
    ! [X23] : k4_xboole_0(k1_xboole_0,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_20,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X25,X26] :
      ( ~ r1_xboole_0(k1_tarski(X25),X26)
      | ~ r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_32,plain,(
    ! [X24] : r1_xboole_0(X24,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

cnf(c_0_35,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,X28)
        | ~ r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))) )
      & ( X27 != X29
        | ~ r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))) )
      & ( ~ r2_hidden(X27,X28)
        | X27 = X29
        | r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_39,plain,(
    ! [X37] : u1_struct_0(k3_yellow_1(X37)) = k9_setfam_1(X37) ),
    inference(variable_rename,[status(thm)],[t4_waybel_7])).

fof(c_0_40,plain,(
    ! [X33] : k9_setfam_1(X33) = k1_zfmisc_1(X33) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_41,plain,(
    ! [X36] : k3_yellow_1(X36) = k3_lattice3(k1_lattice3(X36)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t15_yellow19])).

cnf(c_0_43,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_54,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k7_subset_1(X30,X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_55,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    & v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    & esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_42])])])])).

cnf(c_0_59,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_63,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_47])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)
    | v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_51])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_69,plain,
    ( X1 = X3
    | r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_24])).

fof(c_0_70,plain,(
    ! [X38,X39] :
      ( v2_struct_0(X38)
      | ~ l1_struct_0(X38)
      | v1_xboole_0(X39)
      | ~ v2_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))
      | ~ v13_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X38)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X38))),X39,k1_tarski(k1_xboole_0)) = k2_yellow19(X38,k3_yellow19(X38,k2_struct_0(X38),X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_71,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_72,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X1))) = k1_zfmisc_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k1_tarski(X2)))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_24])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_76,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_61])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_47]),c_0_64])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k3_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( esk1_1(X1) = X2
    | r2_hidden(esk1_1(X1),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2))))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_49])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_34])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_85,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_24])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_57]),c_0_72])).

fof(c_0_87,plain,(
    ! [X40,X41,X42] :
      ( v1_xboole_0(X40)
      | v1_xboole_0(X41)
      | ~ v1_subset_1(X41,u1_struct_0(k3_yellow_1(X40)))
      | ~ v2_waybel_0(X41,k3_yellow_1(X40))
      | ~ v13_waybel_0(X41,k3_yellow_1(X40))
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40))))
      | ~ r2_hidden(X42,X41)
      | ~ v1_xboole_0(X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_88,plain,(
    ! [X34] :
      ( ~ l1_struct_0(X34)
      | k2_struct_0(X34) = u1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X1)))) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_92,plain,
    ( r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),k5_xboole_0(X1,k3_xboole_0(X1,X3)))
    | r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)
    | v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_66])).

cnf(c_0_93,plain,
    ( esk1_1(X1) = X2
    | v1_xboole_0(X1)
    | ~ r2_hidden(esk1_1(X1),k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_80])).

cnf(c_0_94,plain,
    ( r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X1)
    | v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_49])).

cnf(c_0_95,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_72])).

cnf(c_0_96,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_57])).

cnf(c_0_97,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_57])).

cnf(c_0_98,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_99,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_101,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))),esk4_0,X1) = k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_102,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_103,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ l1_struct_0(X35)
      | ~ v1_xboole_0(u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_104,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_105,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_51,c_0_91])).

cnf(c_0_107,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_108,plain,
    ( r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)
    | v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_92]),c_0_34]),c_0_34])).

cnf(c_0_109,plain,
    ( esk1_1(k3_xboole_0(k1_tarski(X1),X2)) = X1
    | v1_xboole_0(k3_xboole_0(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_110,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_111,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0))) = k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98]),c_0_86])]),c_0_99]),c_0_100]),c_0_101])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_113,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_72])).

cnf(c_0_114,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_115,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(esk3_0) = k2_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_98])).

cnf(c_0_117,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_67]),c_0_81])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107])])).

cnf(c_0_119,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(k3_xboole_0(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_120,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_110,c_0_24])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_111]),c_0_112])).

cnf(c_0_122,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_113,c_0_44])).

cnf(c_0_123,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_114,c_0_57])).

cnf(c_0_124,negated_conjecture,
    ( ~ v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_98])]),c_0_99])).

cnf(c_0_125,plain,
    ( esk1_1(k1_tarski(X1)) = X1
    | v1_xboole_0(k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_67]),c_0_117])).

cnf(c_0_126,plain,
    ( r2_hidden(X1,k1_tarski(X2))
    | ~ r2_hidden(X2,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0),k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_111]),c_0_121])]),c_0_112])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_96]),c_0_123]),c_0_97]),c_0_86])]),c_0_124])).

cnf(c_0_129,plain,
    ( X1 = X2
    | v1_xboole_0(k1_tarski(X1))
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_tarski(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( ~ v1_xboole_0(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_121])).

cnf(c_0_133,negated_conjecture,
    ( esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133]),c_0_107])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 5.35/5.57  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 5.35/5.57  # and selection function SelectNewComplexAHPNS.
% 5.35/5.57  #
% 5.35/5.57  # Preprocessing time       : 0.028 s
% 5.35/5.57  # Presaturation interreduction done
% 5.35/5.57  
% 5.35/5.57  # Proof found!
% 5.35/5.57  # SZS status Theorem
% 5.35/5.57  # SZS output start CNFRefutation
% 5.35/5.57  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.35/5.57  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.35/5.57  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.35/5.57  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.35/5.57  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.35/5.57  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.35/5.57  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 5.35/5.57  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.35/5.57  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.35/5.57  fof(t4_waybel_7, axiom, ![X1]:u1_struct_0(k3_yellow_1(X1))=k9_setfam_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_7)).
% 5.35/5.57  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 5.35/5.57  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 5.35/5.57  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 5.35/5.57  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.35/5.57  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 5.35/5.57  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 5.35/5.57  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.35/5.57  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.35/5.57  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.35/5.57  fof(c_0_19, plain, ![X23]:k4_xboole_0(k1_xboole_0,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 5.35/5.57  fof(c_0_20, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 5.35/5.57  fof(c_0_21, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 5.35/5.57  fof(c_0_22, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 5.35/5.57  cnf(c_0_23, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.35/5.57  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.35/5.57  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.35/5.57  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.35/5.57  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.35/5.57  fof(c_0_28, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 5.35/5.57  cnf(c_0_29, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.35/5.57  fof(c_0_30, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 5.35/5.57  fof(c_0_31, plain, ![X25, X26]:(~r1_xboole_0(k1_tarski(X25),X26)|~r2_hidden(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 5.35/5.57  fof(c_0_32, plain, ![X24]:r1_xboole_0(X24,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 5.35/5.57  cnf(c_0_33, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 5.35/5.57  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 5.35/5.57  cnf(c_0_35, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 5.35/5.57  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_27, c_0_24])).
% 5.35/5.57  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 5.35/5.57  fof(c_0_38, plain, ![X27, X28, X29]:(((r2_hidden(X27,X28)|~r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))))&(X27!=X29|~r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29)))))&(~r2_hidden(X27,X28)|X27=X29|r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 5.35/5.57  fof(c_0_39, plain, ![X37]:u1_struct_0(k3_yellow_1(X37))=k9_setfam_1(X37), inference(variable_rename,[status(thm)],[t4_waybel_7])).
% 5.35/5.57  fof(c_0_40, plain, ![X33]:k9_setfam_1(X33)=k1_zfmisc_1(X33), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 5.35/5.57  fof(c_0_41, plain, ![X36]:k3_yellow_1(X36)=k3_lattice3(k1_lattice3(X36)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 5.35/5.57  fof(c_0_42, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 5.35/5.57  cnf(c_0_43, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 5.35/5.57  cnf(c_0_44, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.35/5.57  cnf(c_0_45, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.35/5.57  cnf(c_0_46, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.35/5.57  cnf(c_0_47, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 5.35/5.57  cnf(c_0_48, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 5.35/5.57  cnf(c_0_49, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.35/5.57  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_36])).
% 5.35/5.57  cnf(c_0_51, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_37, c_0_24])).
% 5.35/5.57  cnf(c_0_52, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.35/5.57  cnf(c_0_53, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.35/5.57  fof(c_0_54, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k7_subset_1(X30,X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 5.35/5.57  cnf(c_0_55, plain, (u1_struct_0(k3_yellow_1(X1))=k9_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 5.35/5.57  cnf(c_0_56, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.35/5.57  cnf(c_0_57, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.35/5.57  fof(c_0_58, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((((~v1_xboole_0(esk4_0)&v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))&v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))))&esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_42])])])])).
% 5.35/5.57  cnf(c_0_59, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.35/5.57  cnf(c_0_60, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_43])).
% 5.35/5.57  cnf(c_0_61, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X3))|r2_hidden(esk2_3(X2,X3,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 5.35/5.57  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 5.35/5.57  cnf(c_0_63, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X3))|r2_hidden(esk2_3(X2,X3,X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 5.35/5.57  cnf(c_0_64, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_47])).
% 5.35/5.57  cnf(c_0_65, plain, (v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 5.35/5.57  cnf(c_0_66, plain, (r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)|v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 5.35/5.57  cnf(c_0_67, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_51])).
% 5.35/5.57  cnf(c_0_68, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_24])).
% 5.35/5.57  cnf(c_0_69, plain, (X1=X3|r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_24])).
% 5.35/5.57  fof(c_0_70, plain, ![X38, X39]:(v2_struct_0(X38)|~l1_struct_0(X38)|(v1_xboole_0(X39)|~v2_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))|~v13_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X38)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X38))),X39,k1_tarski(k1_xboole_0))=k2_yellow19(X38,k3_yellow19(X38,k2_struct_0(X38),X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 5.35/5.57  cnf(c_0_71, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 5.35/5.57  cnf(c_0_72, plain, (u1_struct_0(k3_lattice3(k1_lattice3(X1)))=k1_zfmisc_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 5.35/5.57  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_74, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k1_tarski(X2))))), inference(rw,[status(thm)],[c_0_59, c_0_24])).
% 5.35/5.57  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 5.35/5.57  cnf(c_0_76, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_44, c_0_61])).
% 5.35/5.57  cnf(c_0_77, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_47]), c_0_64])).
% 5.35/5.57  cnf(c_0_78, plain, (v1_xboole_0(k3_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 5.35/5.57  cnf(c_0_79, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_68])).
% 5.35/5.57  cnf(c_0_80, plain, (esk1_1(X1)=X2|r2_hidden(esk1_1(X1),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2))))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_69, c_0_49])).
% 5.35/5.57  cnf(c_0_81, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_50, c_0_34])).
% 5.35/5.57  cnf(c_0_82, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 5.35/5.57  cnf(c_0_83, negated_conjecture, (v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_84, negated_conjecture, (v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_85, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_24])).
% 5.35/5.57  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_57]), c_0_72])).
% 5.35/5.57  fof(c_0_87, plain, ![X40, X41, X42]:(v1_xboole_0(X40)|(v1_xboole_0(X41)|~v1_subset_1(X41,u1_struct_0(k3_yellow_1(X40)))|~v2_waybel_0(X41,k3_yellow_1(X40))|~v13_waybel_0(X41,k3_yellow_1(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40))))|(~r2_hidden(X42,X41)|~v1_xboole_0(X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 5.35/5.57  fof(c_0_88, plain, ![X34]:(~l1_struct_0(X34)|k2_struct_0(X34)=u1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 5.35/5.57  cnf(c_0_89, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X1))))), inference(er,[status(thm)],[c_0_74])).
% 5.35/5.57  cnf(c_0_90, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 5.35/5.57  cnf(c_0_91, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 5.35/5.57  cnf(c_0_92, plain, (r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),k5_xboole_0(X1,k3_xboole_0(X1,X3)))|r2_hidden(esk1_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)|v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_79, c_0_66])).
% 5.35/5.57  cnf(c_0_93, plain, (esk1_1(X1)=X2|v1_xboole_0(X1)|~r2_hidden(esk1_1(X1),k1_tarski(X2))), inference(spm,[status(thm)],[c_0_48, c_0_80])).
% 5.35/5.57  cnf(c_0_94, plain, (r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X1)|v1_xboole_0(k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_81, c_0_49])).
% 5.35/5.57  cnf(c_0_95, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_72])).
% 5.35/5.57  cnf(c_0_96, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_83, c_0_57])).
% 5.35/5.57  cnf(c_0_97, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_84, c_0_57])).
% 5.35/5.57  cnf(c_0_98, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_99, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_100, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_101, negated_conjecture, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))),esk4_0,X1)=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 5.35/5.57  cnf(c_0_102, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 5.35/5.57  fof(c_0_103, plain, ![X35]:(v2_struct_0(X35)|~l1_struct_0(X35)|~v1_xboole_0(u1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 5.35/5.57  cnf(c_0_104, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 5.35/5.57  cnf(c_0_105, plain, (~r2_hidden(X1,k5_xboole_0(X2,X3))|~v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 5.35/5.57  cnf(c_0_106, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_51, c_0_91])).
% 5.35/5.57  cnf(c_0_107, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 5.35/5.57  cnf(c_0_108, plain, (r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)|v1_xboole_0(k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_92]), c_0_34]), c_0_34])).
% 5.35/5.57  cnf(c_0_109, plain, (esk1_1(k3_xboole_0(k1_tarski(X1),X2))=X1|v1_xboole_0(k3_xboole_0(k1_tarski(X1),X2))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 5.35/5.57  cnf(c_0_110, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.35/5.57  cnf(c_0_111, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0)))=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_98]), c_0_86])]), c_0_99]), c_0_100]), c_0_101])).
% 5.35/5.57  cnf(c_0_112, negated_conjecture, (esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_113, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_72])).
% 5.35/5.57  cnf(c_0_114, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.35/5.57  cnf(c_0_115, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 5.35/5.57  cnf(c_0_116, negated_conjecture, (u1_struct_0(esk3_0)=k2_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_104, c_0_98])).
% 5.35/5.57  cnf(c_0_117, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_67]), c_0_81])).
% 5.35/5.57  cnf(c_0_118, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107])])).
% 5.35/5.57  cnf(c_0_119, plain, (r2_hidden(X1,X2)|v1_xboole_0(k3_xboole_0(k1_tarski(X1),X2))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 5.35/5.57  cnf(c_0_120, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_110, c_0_24])).
% 5.35/5.57  cnf(c_0_121, negated_conjecture, (r2_hidden(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_111]), c_0_112])).
% 5.35/5.57  cnf(c_0_122, plain, (v1_xboole_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_113, c_0_44])).
% 5.35/5.57  cnf(c_0_123, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))), inference(rw,[status(thm)],[c_0_114, c_0_57])).
% 5.35/5.57  cnf(c_0_124, negated_conjecture, (~v1_xboole_0(k2_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_98])]), c_0_99])).
% 5.35/5.57  cnf(c_0_125, plain, (esk1_1(k1_tarski(X1))=X1|v1_xboole_0(k1_tarski(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_67]), c_0_117])).
% 5.35/5.57  cnf(c_0_126, plain, (r2_hidden(X1,k1_tarski(X2))|~r2_hidden(X2,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 5.35/5.57  cnf(c_0_127, negated_conjecture, (r2_hidden(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0),k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_111]), c_0_121])]), c_0_112])).
% 5.35/5.57  cnf(c_0_128, negated_conjecture, (~r2_hidden(X1,esk4_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_96]), c_0_123]), c_0_97]), c_0_86])]), c_0_124])).
% 5.35/5.57  cnf(c_0_129, plain, (X1=X2|v1_xboole_0(k1_tarski(X1))|~r2_hidden(X1,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_93, c_0_125])).
% 5.35/5.57  cnf(c_0_130, negated_conjecture, (r2_hidden(k1_xboole_0,k1_tarski(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0)))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 5.35/5.57  cnf(c_0_131, negated_conjecture, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_44, c_0_127])).
% 5.35/5.57  cnf(c_0_132, negated_conjecture, (~v1_xboole_0(esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0))), inference(spm,[status(thm)],[c_0_128, c_0_121])).
% 5.35/5.57  cnf(c_0_133, negated_conjecture, (esk2_3(esk4_0,k1_tarski(k1_xboole_0),esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131])).
% 5.35/5.57  cnf(c_0_134, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_133]), c_0_107])]), ['proof']).
% 5.35/5.57  # SZS output end CNFRefutation
% 5.35/5.57  # Proof object total steps             : 135
% 5.35/5.57  # Proof object clause steps            : 97
% 5.35/5.57  # Proof object formula steps           : 38
% 5.35/5.57  # Proof object conjectures             : 27
% 5.35/5.57  # Proof object clause conjectures      : 24
% 5.35/5.57  # Proof object formula conjectures     : 3
% 5.35/5.57  # Proof object initial clauses used    : 32
% 5.35/5.57  # Proof object initial formulas used   : 19
% 5.35/5.57  # Proof object generating inferences   : 39
% 5.35/5.57  # Proof object simplifying inferences  : 70
% 5.35/5.57  # Training examples: 0 positive, 0 negative
% 5.35/5.57  # Parsed axioms                        : 19
% 5.35/5.57  # Removed by relevancy pruning/SinE    : 0
% 5.35/5.57  # Initial clauses                      : 34
% 5.35/5.57  # Removed in clause preprocessing      : 4
% 5.35/5.57  # Initial clauses in saturation        : 30
% 5.35/5.57  # Processed clauses                    : 4481
% 5.35/5.57  # ...of these trivial                  : 19
% 5.35/5.57  # ...subsumed                          : 3734
% 5.35/5.57  # ...remaining for further processing  : 728
% 5.35/5.57  # Other redundant clauses eliminated   : 80
% 5.35/5.57  # Clauses deleted for lack of memory   : 0
% 5.35/5.57  # Backward-subsumed                    : 28
% 5.35/5.57  # Backward-rewritten                   : 24
% 5.35/5.57  # Generated clauses                    : 326651
% 5.35/5.57  # ...of the previous two non-trivial   : 320385
% 5.35/5.57  # Contextual simplify-reflections      : 43
% 5.35/5.57  # Paramodulations                      : 326289
% 5.35/5.57  # Factorizations                       : 282
% 5.35/5.57  # Equation resolutions                 : 80
% 5.35/5.57  # Propositional unsat checks           : 0
% 5.35/5.57  #    Propositional check models        : 0
% 5.35/5.57  #    Propositional check unsatisfiable : 0
% 5.35/5.57  #    Propositional clauses             : 0
% 5.35/5.57  #    Propositional clauses after purity: 0
% 5.35/5.57  #    Propositional unsat core size     : 0
% 5.35/5.57  #    Propositional preprocessing time  : 0.000
% 5.35/5.57  #    Propositional encoding time       : 0.000
% 5.35/5.57  #    Propositional solver time         : 0.000
% 5.35/5.57  #    Success case prop preproc time    : 0.000
% 5.35/5.57  #    Success case prop encoding time   : 0.000
% 5.35/5.57  #    Success case prop solver time     : 0.000
% 5.35/5.57  # Current number of processed clauses  : 643
% 5.35/5.57  #    Positive orientable unit clauses  : 23
% 5.35/5.57  #    Positive unorientable unit clauses: 0
% 5.35/5.57  #    Negative unit clauses             : 13
% 5.35/5.57  #    Non-unit-clauses                  : 607
% 5.35/5.57  # Current number of unprocessed clauses: 315761
% 5.35/5.57  # ...number of literals in the above   : 2022619
% 5.35/5.57  # Current number of archived formulas  : 0
% 5.35/5.57  # Current number of archived clauses   : 85
% 5.35/5.57  # Clause-clause subsumption calls (NU) : 115553
% 5.35/5.57  # Rec. Clause-clause subsumption calls : 28861
% 5.35/5.57  # Non-unit clause-clause subsumptions  : 3180
% 5.35/5.57  # Unit Clause-clause subsumption calls : 744
% 5.35/5.57  # Rewrite failures with RHS unbound    : 0
% 5.35/5.57  # BW rewrite match attempts            : 73
% 5.35/5.57  # BW rewrite match successes           : 10
% 5.35/5.57  # Condensation attempts                : 0
% 5.35/5.57  # Condensation successes               : 0
% 5.35/5.57  # Termbank termtop insertions          : 10893827
% 5.43/5.59  
% 5.43/5.59  # -------------------------------------------------
% 5.43/5.59  # User time                : 5.111 s
% 5.43/5.59  # System time              : 0.139 s
% 5.43/5.59  # Total time               : 5.251 s
% 5.43/5.59  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
