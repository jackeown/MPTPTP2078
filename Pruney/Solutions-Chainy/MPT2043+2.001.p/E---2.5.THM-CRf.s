%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 345 expanded)
%              Number of clauses        :   46 ( 156 expanded)
%              Number of leaves         :   11 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 ( 794 expanded)
%              Number of equality atoms :   32 ( 263 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_waybel_7,axiom,(
    ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t2_yellow19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
     => ( v13_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r1_tarski(X3,X4)
              & r1_tarski(X4,X1)
              & r2_hidden(X3,X2) )
           => r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_11,plain,(
    ! [X36] : u1_struct_0(k3_yellow_1(X36)) = k9_setfam_1(X36) ),
    inference(variable_rename,[status(thm)],[t4_waybel_7])).

fof(c_0_12,plain,(
    ! [X26] : k9_setfam_1(X26) = k1_zfmisc_1(X26) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_13,plain,(
    ! [X27] : k3_yellow_1(X27) = k3_lattice3(k1_lattice3(X27)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t2_yellow19])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_16,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0)))
    & v2_waybel_0(esk7_0,k3_yellow_1(esk6_0))
    & v13_waybel_0(esk7_0,k3_yellow_1(esk6_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0))))
    & r2_hidden(esk8_0,esk7_0)
    & v1_xboole_0(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_20,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | ~ r1_tarski(esk3_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r1_tarski(esk3_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X1))) = k1_zfmisc_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ( ~ v1_subset_1(X29,X28)
        | X29 != X28
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) )
      & ( X29 = X28
        | v1_subset_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(esk6_0))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_22])).

cnf(c_0_29,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | X2 != u1_struct_0(k3_lattice3(k1_lattice3(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_tarski(esk3_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( X1 != X2
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2)))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2)))) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(k3_lattice3(k1_lattice3(esk6_0))))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_42,plain,
    ( X2 = u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | r2_hidden(esk3_2(X1,X2),X2)
    | r1_tarski(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_43,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2))))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X30)
        | ~ r2_hidden(X32,X31)
        | r2_hidden(X33,X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( r1_tarski(esk4_2(X30,X31),esk5_2(X30,X31))
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( r1_tarski(esk5_2(X30,X31),X30)
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( ~ r2_hidden(esk5_2(X30,X31),X31)
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

fof(c_0_47,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_48,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r1_tarski(esk3_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_subset_1(esk7_0,X1)
    | r1_tarski(esk3_2(esk6_0,X1),esk6_0)
    | r2_hidden(esk3_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_52,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,plain,
    ( X2 = u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r1_tarski(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_2(esk6_0,esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(X4,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X2))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_18]),c_0_18]),c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_18])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(k3_lattice3(k1_lattice3(esk6_0))) = esk7_0
    | ~ r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_28]),c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_62]),c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:01:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S5PRR_RG_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.029 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t4_waybel_7, axiom, ![X1]:u1_struct_0(k3_yellow_1(X1))=k9_setfam_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 0.13/0.40  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.13/0.40  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.40  fof(t2_yellow19, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t11_waybel_7, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))=>(v13_waybel_0(X2,k3_yellow_1(X1))<=>![X3, X4]:(((r1_tarski(X3,X4)&r1_tarski(X4,X1))&r2_hidden(X3,X2))=>r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_7)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(c_0_11, plain, ![X36]:u1_struct_0(k3_yellow_1(X36))=k9_setfam_1(X36), inference(variable_rename,[status(thm)],[t4_waybel_7])).
% 0.13/0.40  fof(c_0_12, plain, ![X26]:k9_setfam_1(X26)=k1_zfmisc_1(X26), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.13/0.40  fof(c_0_13, plain, ![X27]:k3_yellow_1(X27)=k3_lattice3(k1_lattice3(X27)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3)))))), inference(assume_negation,[status(cth)],[t2_yellow19])).
% 0.13/0.40  fof(c_0_15, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  cnf(c_0_16, plain, (u1_struct_0(k3_yellow_1(X1))=k9_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_17, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_18, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk6_0)&(((((~v1_xboole_0(esk7_0)&v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0))))&v2_waybel_0(esk7_0,k3_yellow_1(esk6_0)))&v13_waybel_0(esk7_0,k3_yellow_1(esk6_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0)))))&(r2_hidden(esk8_0,esk7_0)&v1_xboole_0(esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.40  fof(c_0_20, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk3_2(X21,X22),X22)|~r1_tarski(esk3_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk3_2(X21,X22),X22)|r1_tarski(esk3_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.40  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_22, plain, (u1_struct_0(k3_lattice3(k1_lattice3(X1)))=k1_zfmisc_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  fof(c_0_24, plain, ![X28, X29]:((~v1_subset_1(X29,X28)|X29!=X28|~m1_subset_1(X29,k1_zfmisc_1(X28)))&(X29=X28|v1_subset_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  fof(c_0_26, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2))))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(esk6_0)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_22])).
% 0.13/0.40  cnf(c_0_29, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  fof(c_0_30, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  cnf(c_0_31, plain, (r1_tarski(X1,X3)|X2!=u1_struct_0(k3_lattice3(k1_lattice3(X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_22])).
% 0.13/0.40  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(esk6_0))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_35, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_tarski(esk3_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_36, plain, (X1!=X2|~v1_subset_1(X1,X2)|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2))))), inference(rw,[status(thm)],[c_0_29, c_0_22])).
% 0.13/0.40  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2))))), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,u1_struct_0(k3_lattice3(k1_lattice3(esk6_0))))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(esk6_0))))), inference(rw,[status(thm)],[c_0_34, c_0_18])).
% 0.13/0.40  cnf(c_0_42, plain, (X2=u1_struct_0(k3_lattice3(k1_lattice3(X1)))|r2_hidden(esk3_2(X1,X2),X2)|r1_tarski(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[c_0_35, c_0_22])).
% 0.13/0.40  cnf(c_0_43, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X1))))), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_44, plain, (m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_22])).
% 0.13/0.40  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.40  fof(c_0_46, plain, ![X30, X31, X32, X33]:((~v13_waybel_0(X31,k3_yellow_1(X30))|(~r1_tarski(X32,X33)|~r1_tarski(X33,X30)|~r2_hidden(X32,X31)|r2_hidden(X33,X31))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))))&((((r1_tarski(esk4_2(X30,X31),esk5_2(X30,X31))|v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))))&(r1_tarski(esk5_2(X30,X31),X30)|v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30))))))&(r2_hidden(esk4_2(X30,X31),X31)|v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30))))))&(~r2_hidden(esk5_2(X30,X31),X31)|v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).
% 0.13/0.40  fof(c_0_47, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_48, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r1_tarski(esk3_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (v1_subset_1(esk7_0,X1)|r1_tarski(esk3_2(esk6_0,X1),esk6_0)|r2_hidden(esk3_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.40  cnf(c_0_51, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.40  cnf(c_0_52, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,k3_yellow_1(X2))|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_54, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.40  cnf(c_0_55, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_56, plain, (X2=u1_struct_0(k3_lattice3(k1_lattice3(X1)))|~r2_hidden(esk3_2(X1,X2),X2)|~r1_tarski(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[c_0_48, c_0_22])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_2(esk6_0,esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.13/0.40  cnf(c_0_58, plain, (r2_hidden(X4,X1)|~r2_hidden(X3,X1)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)|~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_18]), c_0_18]), c_0_22])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(esk6_0)))), inference(rw,[status(thm)],[c_0_53, c_0_18])).
% 0.13/0.40  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (u1_struct_0(k3_lattice3(k1_lattice3(esk6_0)))=esk7_0|~r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk7_0)|~r1_tarski(X1,esk6_0)|~r1_tarski(X2,X1)|~r2_hidden(X2,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_28]), c_0_59])])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_62]), c_0_51])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,esk7_0)|~r1_tarski(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_57])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 69
% 0.13/0.40  # Proof object clause steps            : 46
% 0.13/0.40  # Proof object formula steps           : 23
% 0.13/0.40  # Proof object conjectures             : 22
% 0.13/0.40  # Proof object clause conjectures      : 19
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 19
% 0.13/0.40  # Proof object initial formulas used   : 11
% 0.13/0.40  # Proof object generating inferences   : 14
% 0.13/0.40  # Proof object simplifying inferences  : 27
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 11
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 32
% 0.13/0.40  # Removed in clause preprocessing      : 3
% 0.13/0.40  # Initial clauses in saturation        : 29
% 0.13/0.40  # Processed clauses                    : 124
% 0.13/0.40  # ...of these trivial                  : 6
% 0.13/0.40  # ...subsumed                          : 11
% 0.13/0.40  # ...remaining for further processing  : 107
% 0.13/0.40  # Other redundant clauses eliminated   : 11
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 12
% 0.13/0.40  # Backward-rewritten                   : 3
% 0.13/0.40  # Generated clauses                    : 786
% 0.13/0.40  # ...of the previous two non-trivial   : 723
% 0.13/0.40  # Contextual simplify-reflections      : 2
% 0.13/0.40  # Paramodulations                      : 765
% 0.13/0.40  # Factorizations                       : 8
% 0.13/0.40  # Equation resolutions                 : 13
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 89
% 0.13/0.40  #    Positive orientable unit clauses  : 12
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 73
% 0.13/0.40  # Current number of unprocessed clauses: 616
% 0.13/0.40  # ...number of literals in the above   : 3341
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 18
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1471
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 822
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 17
% 0.13/0.40  # Unit Clause-clause subsumption calls : 61
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 12
% 0.13/0.40  # BW rewrite match successes           : 2
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 15319
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.055 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.060 s
% 0.13/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
