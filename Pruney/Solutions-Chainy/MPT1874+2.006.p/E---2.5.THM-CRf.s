%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 103 expanded)
%              Number of clauses        :   34 (  40 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 456 expanded)
%              Number of equality atoms :   18 (  54 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t41_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tex_2(X2,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( r2_hidden(X3,X2)
                   => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_tex_2])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & v2_tex_2(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & r2_hidden(esk6_0,esk5_0)
    & k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) != k6_domain_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_tex_2(X26,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r1_tarski(X27,X26)
        | k9_subset_1(u1_struct_0(X25),X26,k2_pre_topc(X25,X27)) = X27
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk3_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( r1_tarski(esk3_2(X25,X26),X26)
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( k9_subset_1(u1_struct_0(X25),X26,k2_pre_topc(X25,esk3_2(X25,X26))) != esk3_2(X25,X26)
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) != k6_domain_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)) = X3
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(pm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tarski(k1_tarski(X17),X18)
        | r2_hidden(X17,X18) )
      & ( ~ r2_hidden(X17,X18)
        | r1_tarski(k1_tarski(X17),X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_29,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X15,X16] : k2_enumset1(X15,X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_31,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ m1_subset_1(X24,X23)
      | k6_domain_1(X23,X24) = k1_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_32,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_15])]),c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk4_0)),esk5_0) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(pm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X19,X20] :
      ( ~ v1_xboole_0(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | v1_xboole_0(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(pm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( k6_domain_1(X1,X2) = k2_enumset1(X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(pm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) ),
    inference(pm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k6_domain_1(X1,X2),X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(pm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_15]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_43])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:50:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.19/0.41  # and selection function NoSelection.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.043 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t42_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 0.19/0.42  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.42  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.42  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.42  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t42_tex_2])).
% 0.19/0.42  fof(c_0_11, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(v2_tex_2(esk5_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(r2_hidden(esk6_0,esk5_0)&k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))!=k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.42  fof(c_0_13, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  fof(c_0_16, plain, ![X25, X26, X27]:((~v2_tex_2(X26,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~r1_tarski(X27,X26)|k9_subset_1(u1_struct_0(X25),X26,k2_pre_topc(X25,X27))=X27))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((m1_subset_1(esk3_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((r1_tarski(esk3_2(X25,X26),X26)|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(k9_subset_1(u1_struct_0(X25),X26,k2_pre_topc(X25,esk3_2(X25,X26)))!=esk3_2(X25,X26)|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 0.19/0.42  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_18, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(pm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.42  cnf(c_0_19, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))!=k6_domain_1(u1_struct_0(esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_20, plain, (k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3))=X3|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_21, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(pm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.42  cnf(c_0_27, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_28, plain, ![X17, X18]:((~r1_tarski(k1_tarski(X17),X18)|r2_hidden(X17,X18))&(~r2_hidden(X17,X18)|r1_tarski(k1_tarski(X17),X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.42  fof(c_0_29, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  fof(c_0_30, plain, ![X15, X16]:k2_enumset1(X15,X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.42  fof(c_0_31, plain, ![X23, X24]:(v1_xboole_0(X23)|~m1_subset_1(X24,X23)|k6_domain_1(X23,X24)=k1_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.42  fof(c_0_32, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_15])]), c_0_24])).
% 0.19/0.42  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r2_hidden(esk2_2(X1,u1_struct_0(esk4_0)),esk5_0)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.42  cnf(c_0_36, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X1,X3)), inference(pm,[status(thm)],[c_0_17, c_0_27])).
% 0.19/0.42  cnf(c_0_37, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_40, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  fof(c_0_41, plain, ![X19, X20]:(~v1_xboole_0(X19)|(~m1_subset_1(X20,k1_zfmisc_1(X19))|v1_xboole_0(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.42  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,esk5_0)), inference(pm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.42  cnf(c_0_46, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.42  cnf(c_0_47, plain, (k6_domain_1(X1,X2)=k2_enumset1(X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_38]), c_0_39])).
% 0.19/0.42  cnf(c_0_48, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(pm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)), inference(pm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.42  cnf(c_0_51, plain, (r1_tarski(k6_domain_1(X1,X2),X3)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~r2_hidden(X2,X3)), inference(pm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_15]), c_0_49])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_43])]), c_0_53]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 55
% 0.19/0.42  # Proof object clause steps            : 34
% 0.19/0.42  # Proof object formula steps           : 21
% 0.19/0.42  # Proof object conjectures             : 21
% 0.19/0.42  # Proof object clause conjectures      : 18
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 20
% 0.19/0.42  # Proof object initial formulas used   : 10
% 0.19/0.42  # Proof object generating inferences   : 12
% 0.19/0.42  # Proof object simplifying inferences  : 15
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 10
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 25
% 0.19/0.42  # Removed in clause preprocessing      : 2
% 0.19/0.42  # Initial clauses in saturation        : 23
% 0.19/0.42  # Processed clauses                    : 244
% 0.19/0.42  # ...of these trivial                  : 0
% 0.19/0.42  # ...subsumed                          : 157
% 0.19/0.42  # ...remaining for further processing  : 87
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 4
% 0.19/0.42  # Backward-rewritten                   : 0
% 0.19/0.42  # Generated clauses                    : 694
% 0.19/0.42  # ...of the previous two non-trivial   : 647
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 694
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 83
% 0.19/0.42  #    Positive orientable unit clauses  : 10
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 7
% 0.19/0.42  #    Non-unit-clauses                  : 66
% 0.19/0.42  # Current number of unprocessed clauses: 403
% 0.19/0.42  # ...number of literals in the above   : 1928
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 6
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 671
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 550
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 103
% 0.19/0.42  # Unit Clause-clause subsumption calls : 67
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 5
% 0.19/0.42  # BW rewrite match successes           : 0
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 6715
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.065 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.070 s
% 0.19/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
