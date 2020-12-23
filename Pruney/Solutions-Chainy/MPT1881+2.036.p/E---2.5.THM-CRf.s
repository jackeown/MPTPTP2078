%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:35 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 546 expanded)
%              Number of clauses        :   45 ( 215 expanded)
%              Number of leaves         :   10 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 (2600 expanded)
%              Number of equality atoms :   29 ( 156 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t43_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(t27_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( X2 = u1_struct_0(X1)
           => ( v2_tex_2(X2,X1)
            <=> v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tex_2(X2,X1)
            <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tex_2])).

fof(c_0_11,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ r2_hidden(X16,X15)
      | r2_hidden(X16,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v1_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_tex_2(esk4_0,esk3_0)
      | v1_subset_1(esk4_0,u1_struct_0(esk3_0)) )
    & ( v3_tex_2(esk4_0,esk3_0)
      | ~ v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ( ~ v1_subset_1(X18,X17)
        | X18 != X17
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17)) )
      & ( X18 = X17
        | v1_subset_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_17,plain,(
    ! [X19,X20,X21] :
      ( ( v2_tex_2(X20,X19)
        | ~ v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X21,X19)
        | ~ r1_tarski(X20,X21)
        | X20 = X21
        | ~ v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( v2_tex_2(esk2_2(X19,X20),X19)
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(X20,esk2_2(X19,X20))
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( X20 != esk2_2(X19,X20)
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X13] : m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_19,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ v1_tdlat_3(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | v2_tex_2(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

cnf(c_0_24,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | ~ v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0
    | v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

fof(c_0_32,plain,(
    ! [X23,X24] :
      ( ( ~ v2_tex_2(X24,X23)
        | v1_tdlat_3(X23)
        | X24 != u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v1_tdlat_3(X23)
        | v2_tex_2(X24,X23)
        | X24 != u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk4_0
    | ~ v2_tex_2(X1,esk3_0)
    | ~ v3_tex_2(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_15]),c_0_25])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0
    | v3_tex_2(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_34]),c_0_35]),c_0_25])]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0
    | ~ v2_tex_2(u1_struct_0(esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(u1_struct_0(X1),X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_38])])).

cnf(c_0_47,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | m1_subset_1(esk2_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_15]),c_0_44]),c_0_25])])).

cnf(c_0_49,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(esk3_0))
    | ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_35]),c_0_25])]),c_0_36])).

cnf(c_0_51,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_38])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,esk2_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk2_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk2_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_56,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | r1_tarski(esk4_0,esk2_2(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_15]),c_0_44]),c_0_25])])).

cnf(c_0_58,plain,
    ( v3_tex_2(u1_struct_0(X1),X1)
    | esk2_2(X1,u1_struct_0(X1)) != u1_struct_0(X1)
    | ~ v2_tex_2(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_50]),c_0_55])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[c_0_57,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) != esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_44]),c_0_25])]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_2(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(esk2_2(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk2_2(esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n006.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 12:33:37 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.10/0.35  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.10/0.35  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.10/0.35  #
% 0.10/0.35  # Preprocessing time       : 0.029 s
% 0.10/0.35  # Presaturation interreduction done
% 0.10/0.35  
% 0.10/0.35  # Proof found!
% 0.10/0.35  # SZS status Theorem
% 0.10/0.35  # SZS output start CNFRefutation
% 0.10/0.35  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 0.10/0.35  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.10/0.35  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.10/0.35  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.10/0.35  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.10/0.35  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.10/0.35  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.10/0.35  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 0.10/0.35  fof(t27_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(X2=u1_struct_0(X1)=>(v2_tex_2(X2,X1)<=>v1_tdlat_3(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 0.10/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.10/0.35  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.10/0.35  fof(c_0_11, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|(~r2_hidden(X16,X15)|r2_hidden(X16,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.10/0.35  fof(c_0_12, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v1_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_tex_2(esk4_0,esk3_0)|v1_subset_1(esk4_0,u1_struct_0(esk3_0)))&(v3_tex_2(esk4_0,esk3_0)|~v1_subset_1(esk4_0,u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.10/0.35  fof(c_0_13, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.10/0.35  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.35  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  fof(c_0_16, plain, ![X17, X18]:((~v1_subset_1(X18,X17)|X18!=X17|~m1_subset_1(X18,k1_zfmisc_1(X17)))&(X18=X17|v1_subset_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.10/0.35  fof(c_0_17, plain, ![X19, X20, X21]:(((v2_tex_2(X20,X19)|~v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~v2_tex_2(X21,X19)|~r1_tarski(X20,X21)|X20=X21)|~v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19)))&((m1_subset_1(esk2_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(((v2_tex_2(esk2_2(X19,X20),X19)|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(r1_tarski(X20,esk2_2(X19,X20))|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19)))&(X20!=esk2_2(X19,X20)|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.10/0.35  fof(c_0_18, plain, ![X13]:m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.10/0.35  fof(c_0_19, plain, ![X12]:k2_subset_1(X12)=X12, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.10/0.35  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.35  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.10/0.35  cnf(c_0_22, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.10/0.35  fof(c_0_23, plain, ![X25, X26]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~v1_tdlat_3(X25)|~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v2_tex_2(X26,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.10/0.35  cnf(c_0_24, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.35  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_26, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.35  cnf(c_0_27, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.10/0.35  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.10/0.35  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.35  cnf(c_0_30, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|~v1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_31, negated_conjecture, (u1_struct_0(esk3_0)=esk4_0|v1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_15])).
% 0.10/0.35  fof(c_0_32, plain, ![X23, X24]:((~v2_tex_2(X24,X23)|v1_tdlat_3(X23)|X24!=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X23)|~l1_pre_topc(X23)))&(~v1_tdlat_3(X23)|v2_tex_2(X24,X23)|X24!=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).
% 0.10/0.35  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.10/0.35  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_35, negated_conjecture, (v1_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_37, negated_conjecture, (X1=esk4_0|~v2_tex_2(X1,esk3_0)|~v3_tex_2(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_15]), c_0_25])])).
% 0.10/0.35  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.10/0.35  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.10/0.35  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk3_0)=esk4_0|v3_tex_2(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.10/0.35  cnf(c_0_41, plain, (v2_tex_2(X2,X1)|v2_struct_0(X1)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.10/0.35  cnf(c_0_42, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.10/0.35  cnf(c_0_43, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.35  cnf(c_0_44, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_15]), c_0_34]), c_0_35]), c_0_25])]), c_0_36])).
% 0.10/0.35  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk3_0)=esk4_0|~v2_tex_2(u1_struct_0(esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])]), c_0_40])).
% 0.10/0.35  cnf(c_0_46, plain, (v2_struct_0(X1)|v2_tex_2(u1_struct_0(X1),X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_38])])).
% 0.10/0.35  cnf(c_0_47, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_42])).
% 0.10/0.35  cnf(c_0_48, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|m1_subset_1(esk2_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_15]), c_0_44]), c_0_25])])).
% 0.10/0.35  cnf(c_0_49, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(esk3_0))|~v3_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk3_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_35]), c_0_25])]), c_0_36])).
% 0.10/0.35  cnf(c_0_51, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_38])])).
% 0.10/0.35  cnf(c_0_52, plain, (r1_tarski(X1,esk2_2(X2,X1))|v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.35  cnf(c_0_53, plain, (v3_tex_2(X1,X2)|X1!=esk2_2(X2,X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.35  cnf(c_0_54, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk2_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_48])).
% 0.10/0.35  cnf(c_0_55, negated_conjecture, (~v3_tex_2(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.10/0.35  fof(c_0_56, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.10/0.35  cnf(c_0_57, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|r1_tarski(esk4_0,esk2_2(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_15]), c_0_44]), c_0_25])])).
% 0.10/0.35  cnf(c_0_58, plain, (v3_tex_2(u1_struct_0(X1),X1)|esk2_2(X1,u1_struct_0(X1))!=u1_struct_0(X1)|~v2_tex_2(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_38])).
% 0.10/0.35  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk2_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_50]), c_0_55])).
% 0.10/0.35  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.10/0.35  cnf(c_0_61, negated_conjecture, (r1_tarski(esk4_0,esk2_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[c_0_57, c_0_55])).
% 0.10/0.35  cnf(c_0_62, negated_conjecture, (esk2_2(esk3_0,esk4_0)!=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_44]), c_0_25])]), c_0_55])).
% 0.10/0.35  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(esk2_2(esk3_0,esk4_0),X1),esk4_0)|r1_tarski(esk2_2(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_29])).
% 0.10/0.35  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk2_2(esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.10/0.35  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_63]), c_0_64]), ['proof']).
% 0.10/0.35  # SZS output end CNFRefutation
% 0.10/0.35  # Proof object total steps             : 66
% 0.10/0.35  # Proof object clause steps            : 45
% 0.10/0.35  # Proof object formula steps           : 21
% 0.10/0.35  # Proof object conjectures             : 29
% 0.10/0.35  # Proof object clause conjectures      : 26
% 0.10/0.35  # Proof object formula conjectures     : 3
% 0.10/0.35  # Proof object initial clauses used    : 21
% 0.10/0.35  # Proof object initial formulas used   : 10
% 0.10/0.35  # Proof object generating inferences   : 17
% 0.10/0.35  # Proof object simplifying inferences  : 38
% 0.10/0.35  # Training examples: 0 positive, 0 negative
% 0.10/0.35  # Parsed axioms                        : 10
% 0.10/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.35  # Initial clauses                      : 27
% 0.10/0.35  # Removed in clause preprocessing      : 1
% 0.10/0.35  # Initial clauses in saturation        : 26
% 0.10/0.35  # Processed clauses                    : 111
% 0.10/0.35  # ...of these trivial                  : 3
% 0.10/0.35  # ...subsumed                          : 12
% 0.10/0.35  # ...remaining for further processing  : 96
% 0.10/0.35  # Other redundant clauses eliminated   : 5
% 0.10/0.35  # Clauses deleted for lack of memory   : 0
% 0.10/0.35  # Backward-subsumed                    : 1
% 0.10/0.35  # Backward-rewritten                   : 16
% 0.10/0.35  # Generated clauses                    : 84
% 0.10/0.35  # ...of the previous two non-trivial   : 75
% 0.10/0.35  # Contextual simplify-reflections      : 5
% 0.10/0.35  # Paramodulations                      : 76
% 0.10/0.35  # Factorizations                       : 0
% 0.10/0.36  # Equation resolutions                 : 5
% 0.10/0.36  # Propositional unsat checks           : 0
% 0.10/0.36  #    Propositional check models        : 0
% 0.10/0.36  #    Propositional check unsatisfiable : 0
% 0.10/0.36  #    Propositional clauses             : 0
% 0.10/0.36  #    Propositional clauses after purity: 0
% 0.10/0.36  #    Propositional unsat core size     : 0
% 0.10/0.36  #    Propositional preprocessing time  : 0.000
% 0.10/0.36  #    Propositional encoding time       : 0.000
% 0.10/0.36  #    Propositional solver time         : 0.000
% 0.10/0.36  #    Success case prop preproc time    : 0.000
% 0.10/0.36  #    Success case prop encoding time   : 0.000
% 0.10/0.36  #    Success case prop solver time     : 0.000
% 0.10/0.36  # Current number of processed clauses  : 46
% 0.10/0.36  #    Positive orientable unit clauses  : 11
% 0.10/0.36  #    Positive unorientable unit clauses: 0
% 0.10/0.36  #    Negative unit clauses             : 5
% 0.10/0.36  #    Non-unit-clauses                  : 30
% 0.10/0.36  # Current number of unprocessed clauses: 13
% 0.10/0.36  # ...number of literals in the above   : 54
% 0.10/0.36  # Current number of archived formulas  : 0
% 0.10/0.36  # Current number of archived clauses   : 46
% 0.10/0.36  # Clause-clause subsumption calls (NU) : 276
% 0.10/0.36  # Rec. Clause-clause subsumption calls : 110
% 0.10/0.36  # Non-unit clause-clause subsumptions  : 15
% 0.10/0.36  # Unit Clause-clause subsumption calls : 58
% 0.10/0.36  # Rewrite failures with RHS unbound    : 0
% 0.10/0.36  # BW rewrite match attempts            : 5
% 0.10/0.36  # BW rewrite match successes           : 3
% 0.10/0.36  # Condensation attempts                : 0
% 0.10/0.36  # Condensation successes               : 0
% 0.10/0.36  # Termbank termtop insertions          : 3576
% 0.10/0.36  
% 0.10/0.36  # -------------------------------------------------
% 0.10/0.36  # User time                : 0.036 s
% 0.10/0.36  # System time              : 0.002 s
% 0.10/0.36  # Total time               : 0.038 s
% 0.10/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
