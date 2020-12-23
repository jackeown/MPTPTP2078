%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  90 expanded)
%              Number of clauses        :   29 (  39 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 303 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(t28_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_tarski(X3,X2)
                  & v2_tex_2(X2,X1) )
               => v2_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

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

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_10,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_11,plain,(
    ! [X17] : k2_subset_1(X17) = X17 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_12,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t43_tex_2])).

cnf(c_0_23,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v1_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ r1_tarski(X25,X24)
      | ~ v2_tex_2(X24,X23)
      | v2_tex_2(X25,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ( ~ v2_tex_2(X22,X21)
        | v1_tdlat_3(X21)
        | X22 != u1_struct_0(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ v1_tdlat_3(X21)
        | v2_tex_2(X22,X21)
        | X22 != u1_struct_0(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_34])]),c_0_35])).

cnf(c_0_41,plain,
    ( v2_tex_2(u1_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20]),c_0_42]),c_0_34])]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.20/0.40  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.051 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(t43_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 0.20/0.40  fof(t28_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v2_tex_2(X2,X1))=>v2_tex_2(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 0.20/0.40  fof(t27_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(X2=u1_struct_0(X1)=>(v2_tex_2(X2,X1)<=>v1_tdlat_3(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 0.20/0.40  fof(c_0_9, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.40  fof(c_0_11, plain, ![X17]:k2_subset_1(X17)=X17, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.40  fof(c_0_12, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  fof(c_0_14, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.40  cnf(c_0_15, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_16, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_18, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_19, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  fof(c_0_21, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  fof(c_0_22, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t43_tex_2])).
% 0.20/0.40  cnf(c_0_23, plain, (~r1_tarski(X1,X2)|~v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  cnf(c_0_24, plain, (r2_hidden(X1,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  fof(c_0_26, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v1_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&~v2_tex_2(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.20/0.40  cnf(c_0_27, plain, (r2_hidden(X1,k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.40  fof(c_0_29, plain, ![X23, X24, X25]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~r1_tarski(X25,X24)|~v2_tex_2(X24,X23)|v2_tex_2(X25,X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).
% 0.20/0.40  fof(c_0_30, plain, ![X21, X22]:((~v2_tex_2(X22,X21)|v1_tdlat_3(X21)|X22!=u1_struct_0(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~l1_pre_topc(X21)))&(~v1_tdlat_3(X21)|v2_tex_2(X22,X21)|X22!=u1_struct_0(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_32, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_33, plain, (v2_tex_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_36, plain, (v2_tex_2(X2,X1)|v2_struct_0(X1)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_31])).
% 0.20/0.40  cnf(c_0_39, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_32])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_31]), c_0_34])]), c_0_35])).
% 0.20/0.40  cnf(c_0_41, plain, (v2_tex_2(u1_struct_0(X1),X1)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_20])])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (v1_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (~r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20]), c_0_42]), c_0_34])]), c_0_43])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 48
% 0.20/0.40  # Proof object clause steps            : 29
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 13
% 0.20/0.40  # Proof object clause conjectures      : 10
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 14
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 12
% 0.20/0.40  # Proof object simplifying inferences  : 14
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 21
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 20
% 0.20/0.40  # Processed clauses                    : 58
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 1
% 0.20/0.40  # ...remaining for further processing  : 56
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 1
% 0.20/0.40  # Backward-rewritten                   : 1
% 0.20/0.40  # Generated clauses                    : 42
% 0.20/0.40  # ...of the previous two non-trivial   : 33
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 34
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 31
% 0.20/0.40  #    Positive orientable unit clauses  : 8
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 19
% 0.20/0.40  # Current number of unprocessed clauses: 13
% 0.20/0.40  # ...number of literals in the above   : 40
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 24
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 92
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 23
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.40  # Unit Clause-clause subsumption calls : 18
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 9
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 1963
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.060 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
