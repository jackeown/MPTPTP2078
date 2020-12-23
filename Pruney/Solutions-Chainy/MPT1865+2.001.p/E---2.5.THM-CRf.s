%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 100 expanded)
%              Number of clauses        :   26 (  37 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 533 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(d6_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tex_2(X2,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v4_pre_topc(X4,X1)
                              & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_tex_2])).

fof(c_0_9,negated_conjecture,(
    ! [X54] :
      ( l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & v2_tex_2(esk6_0,esk5_0)
      & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
      & r2_hidden(esk7_0,esk6_0)
      & ( ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v4_pre_topc(X54,esk5_0)
        | k9_subset_1(u1_struct_0(esk5_0),esk6_0,X54) != k1_tarski(esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X24] : k2_tarski(X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | k3_xboole_0(X28,k1_tarski(X27)) = k1_tarski(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_12,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v4_pre_topc(X1,esk5_0)
    | k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X45,X46,X47,X50] :
      ( ( m1_subset_1(esk3_3(X45,X46,X47),k1_zfmisc_1(u1_struct_0(X45)))
        | ~ r1_tarski(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ v2_tex_2(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( v4_pre_topc(esk3_3(X45,X46,X47),X45)
        | ~ r1_tarski(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ v2_tex_2(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( k9_subset_1(u1_struct_0(X45),X46,esk3_3(X45,X46,X47)) = X47
        | ~ r1_tarski(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ v2_tex_2(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( m1_subset_1(esk4_2(X45,X46),k1_zfmisc_1(u1_struct_0(X45)))
        | v2_tex_2(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( r1_tarski(esk4_2(X45,X46),X46)
        | v2_tex_2(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ v4_pre_topc(X50,X45)
        | k9_subset_1(u1_struct_0(X45),X46,X50) != esk4_2(X45,X46)
        | v2_tex_2(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

fof(c_0_15,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X29))
      | m1_subset_1(k9_subset_1(X29,X30,X31),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | k9_subset_1(X32,X33,X34) = k3_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_17,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1) != k2_tarski(esk7_0,esk7_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X2,k2_tarski(X1,X1)) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_13]),c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( ~ v4_pre_topc(esk3_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk7_0)),esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])])])).

cnf(c_0_29,plain,
    ( v4_pre_topc(esk3_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(esk3_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X25,X26] :
      ( ( ~ r1_tarski(k1_tarski(X25),X26)
        | r2_hidden(X25,X26) )
      & ( ~ r2_hidden(X25,X26)
        | r1_tarski(k1_tarski(X25),X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:23:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t33_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.13/0.38  fof(d6_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 0.13/0.38  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.13/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t33_tex_2])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ![X54]:(l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(v2_tex_2(esk6_0,esk5_0)&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(r2_hidden(esk7_0,esk6_0)&(~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(esk5_0)))|(~v4_pre_topc(X54,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),esk6_0,X54)!=k1_tarski(esk7_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X24]:k2_tarski(X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_11, plain, ![X27, X28]:(~r2_hidden(X27,X28)|k3_xboole_0(X28,k1_tarski(X27))=k1_tarski(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v4_pre_topc(X1,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_14, plain, ![X45, X46, X47, X50]:(((m1_subset_1(esk3_3(X45,X46,X47),k1_zfmisc_1(u1_struct_0(X45)))|~r1_tarski(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~v2_tex_2(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&((v4_pre_topc(esk3_3(X45,X46,X47),X45)|~r1_tarski(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~v2_tex_2(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&(k9_subset_1(u1_struct_0(X45),X46,esk3_3(X45,X46,X47))=X47|~r1_tarski(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~v2_tex_2(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))))&((m1_subset_1(esk4_2(X45,X46),k1_zfmisc_1(u1_struct_0(X45)))|v2_tex_2(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&((r1_tarski(esk4_2(X45,X46),X46)|v2_tex_2(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X45)))|(~v4_pre_topc(X50,X45)|k9_subset_1(u1_struct_0(X45),X46,X50)!=esk4_2(X45,X46))|v2_tex_2(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X29))|m1_subset_1(k9_subset_1(X29,X30,X31),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.13/0.38  fof(c_0_16, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X32))|k9_subset_1(X32,X33,X34)=k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.13/0.38  fof(c_0_17, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  cnf(c_0_18, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1)!=k2_tarski(esk7_0,esk7_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_24, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, plain, (k3_xboole_0(X2,k2_tarski(X1,X1))=k2_tarski(X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_13]), c_0_13])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (~v4_pre_topc(esk3_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk7_0)),esk5_0)|~m1_subset_1(esk3_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])])])).
% 0.13/0.38  cnf(c_0_29, plain, (v4_pre_topc(esk3_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_30, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_xboole_0(k2_tarski(X1,X1),X2)=k2_tarski(X1,X1)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~m1_subset_1(esk3_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_34, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  fof(c_0_35, plain, ![X25, X26]:((~r1_tarski(k1_tarski(X25),X26)|r2_hidden(X25,X26))&(~r2_hidden(X25,X26)|r1_tarski(k1_tarski(X25),X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (~r1_tarski(k2_tarski(esk7_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.13/0.38  cnf(c_0_41, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_13])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_38])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 43
% 0.13/0.38  # Proof object clause steps            : 26
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 15
% 0.13/0.38  # Proof object clause conjectures      : 12
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 21
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 16
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 37
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 36
% 0.13/0.38  # Processed clauses                    : 243
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 102
% 0.13/0.38  # ...remaining for further processing  : 140
% 0.13/0.38  # Other redundant clauses eliminated   : 12
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 7
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 468
% 0.13/0.38  # ...of the previous two non-trivial   : 423
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 456
% 0.13/0.38  # Factorizations                       : 2
% 0.13/0.38  # Equation resolutions                 : 12
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 126
% 0.13/0.38  #    Positive orientable unit clauses  : 15
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 7
% 0.13/0.38  #    Non-unit-clauses                  : 103
% 0.13/0.38  # Current number of unprocessed clauses: 198
% 0.13/0.38  # ...number of literals in the above   : 764
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 10
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 2784
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1236
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 79
% 0.13/0.38  # Unit Clause-clause subsumption calls : 53
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 13
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8790
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.041 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.048 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
