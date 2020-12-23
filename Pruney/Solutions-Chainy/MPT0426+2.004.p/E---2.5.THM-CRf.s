%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 292 expanded)
%              Number of clauses        :   32 ( 119 expanded)
%              Number of leaves         :    7 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 (1339 expanded)
%              Number of equality atoms :   69 ( 346 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(c_0_7,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X15,X16)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_8,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_15,plain,(
    ! [X19,X20,X21,X22,X23,X25,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X21,X20)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X21,X22)
        | X20 != k1_setfam_1(X19)
        | X19 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X19,X20,X23),X19)
        | r2_hidden(X23,X20)
        | X20 != k1_setfam_1(X19)
        | X19 = k1_xboole_0 )
      & ( ~ r2_hidden(X23,esk2_3(X19,X20,X23))
        | r2_hidden(X23,X20)
        | X20 != k1_setfam_1(X19)
        | X19 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X19,X25),X19)
        | ~ r2_hidden(esk3_2(X19,X25),X25)
        | X25 = k1_setfam_1(X19)
        | X19 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X19,X25),esk4_2(X19,X25))
        | ~ r2_hidden(esk3_2(X19,X25),X25)
        | X25 = k1_setfam_1(X19)
        | X19 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X19,X25),X25)
        | ~ r2_hidden(X28,X19)
        | r2_hidden(esk3_2(X19,X25),X28)
        | X25 = k1_setfam_1(X19)
        | X19 = k1_xboole_0 )
      & ( X30 != k1_setfam_1(X29)
        | X30 = k1_xboole_0
        | X29 != k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | X31 = k1_setfam_1(X29)
        | X29 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_18,negated_conjecture,(
    ! [X38] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))
      & r2_hidden(esk6_0,esk5_0)
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) )
      & ( ~ r2_hidden(esk6_0,esk8_0)
        | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) )
      & ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
        | ~ r2_hidden(X38,esk7_0)
        | r2_hidden(esk6_0,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_10]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(X4)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

fof(c_0_24,plain,(
    ! [X17,X18] :
      ( ( X18 = k1_xboole_0
        | k8_setfam_1(X17,X18) = k6_setfam_1(X17,X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( X18 != k1_xboole_0
        | k8_setfam_1(X17,X18) = X17
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | X2 != k1_setfam_1(esk7_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_27,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk8_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,k1_setfam_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk6_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | ~ r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32)))
      | k6_setfam_1(X32,X33) = k1_setfam_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_3(esk7_0,X1,X2))
    | r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(X2,X1)
    | X1 != k1_setfam_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k6_setfam_1(esk5_0,esk7_0))
    | ~ r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29])]),c_0_34])).

cnf(c_0_41,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k1_setfam_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk6_0,k6_setfam_1(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_29])]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_29])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.37  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.19/0.37  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.19/0.37  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.19/0.37  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.19/0.37  fof(c_0_7, plain, ![X15, X16]:k4_xboole_0(X15,k2_xboole_0(X15,X16))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.37  fof(c_0_8, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.37  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.37  cnf(c_0_10, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_11, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_13, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.19/0.37  fof(c_0_15, plain, ![X19, X20, X21, X22, X23, X25, X28, X29, X30, X31]:((((~r2_hidden(X21,X20)|(~r2_hidden(X22,X19)|r2_hidden(X21,X22))|X20!=k1_setfam_1(X19)|X19=k1_xboole_0)&((r2_hidden(esk2_3(X19,X20,X23),X19)|r2_hidden(X23,X20)|X20!=k1_setfam_1(X19)|X19=k1_xboole_0)&(~r2_hidden(X23,esk2_3(X19,X20,X23))|r2_hidden(X23,X20)|X20!=k1_setfam_1(X19)|X19=k1_xboole_0)))&(((r2_hidden(esk4_2(X19,X25),X19)|~r2_hidden(esk3_2(X19,X25),X25)|X25=k1_setfam_1(X19)|X19=k1_xboole_0)&(~r2_hidden(esk3_2(X19,X25),esk4_2(X19,X25))|~r2_hidden(esk3_2(X19,X25),X25)|X25=k1_setfam_1(X19)|X19=k1_xboole_0))&(r2_hidden(esk3_2(X19,X25),X25)|(~r2_hidden(X28,X19)|r2_hidden(esk3_2(X19,X25),X28))|X25=k1_setfam_1(X19)|X19=k1_xboole_0)))&((X30!=k1_setfam_1(X29)|X30=k1_xboole_0|X29!=k1_xboole_0)&(X31!=k1_xboole_0|X31=k1_setfam_1(X29)|X29!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.19/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_17, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.37  fof(c_0_18, negated_conjecture, ![X38]:(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))&(r2_hidden(esk6_0,esk5_0)&(((r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)))&(~r2_hidden(esk6_0,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))))&(r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|(~r2_hidden(X38,esk7_0)|r2_hidden(esk6_0,X38)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).
% 0.19/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_20, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_10]), c_0_17])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(X4)|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (esk7_0!=k1_xboole_0|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.19/0.37  fof(c_0_24, plain, ![X17, X18]:((X18=k1_xboole_0|k8_setfam_1(X17,X18)=k6_setfam_1(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&(X18!=k1_xboole_0|k8_setfam_1(X17,X18)=X17|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk8_0)|X2!=k1_setfam_1(esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (esk7_0!=k1_xboole_0|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.37  cnf(c_0_27, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk6_0,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|~r2_hidden(X1,k1_setfam_1(esk7_0))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk6_0,X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_33, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|~r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_36, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_37, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32)))|k6_setfam_1(X32,X33)=k1_setfam_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.19/0.37  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk2_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,esk2_3(esk7_0,X1,X2))|r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(X2,X1)|X1!=k1_setfam_1(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk6_0,k6_setfam_1(esk5_0,esk7_0))|~r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29])]), c_0_34])).
% 0.19/0.37  cnf(c_0_41, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk6_0,X1)|X1!=k1_setfam_1(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_29])])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_43])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk6_0,k6_setfam_1(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_29])]), c_0_34])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_29])]), c_0_43]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 47
% 0.19/0.37  # Proof object clause steps            : 32
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 21
% 0.19/0.37  # Proof object clause conjectures      : 18
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 16
% 0.19/0.37  # Proof object simplifying inferences  : 19
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 24
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 24
% 0.19/0.37  # Processed clauses                    : 84
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 12
% 0.19/0.37  # ...remaining for further processing  : 72
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 2
% 0.19/0.37  # Backward-rewritten                   : 12
% 0.19/0.37  # Generated clauses                    : 62
% 0.19/0.37  # ...of the previous two non-trivial   : 63
% 0.19/0.37  # Contextual simplify-reflections      : 3
% 0.19/0.37  # Paramodulations                      : 54
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 8
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 34
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 5
% 0.19/0.37  #    Non-unit-clauses                  : 21
% 0.19/0.37  # Current number of unprocessed clauses: 24
% 0.19/0.37  # ...number of literals in the above   : 82
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 38
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 309
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 165
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.19/0.37  # Unit Clause-clause subsumption calls : 40
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2598
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
