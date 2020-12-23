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
% DateTime   : Thu Dec  3 11:00:53 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 234 expanded)
%              Number of clauses        :   26 (  97 expanded)
%              Number of leaves         :    6 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 938 expanded)
%              Number of equality atoms :   58 ( 103 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X35)
      | ~ r1_tarski(k2_relat_1(X37),X36)
      | m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X40 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != k1_xboole_0
        | v1_funct_2(X40,X38,X39)
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,plain,(
    ! [X26] :
      ( ( k1_relat_1(X26) != k1_xboole_0
        | X26 = k1_xboole_0
        | ~ v1_relat_1(X26) )
      & ( k2_relat_1(X26) != k1_xboole_0
        | X26 = k1_xboole_0
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20]),c_0_20])])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ r1_tarski(k1_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_28,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ r1_tarski(k1_relat_1(X3),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_29,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X3)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X1,X3)
    | X3 != k1_xboole_0
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ r1_tarski(k1_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | k2_relat_1(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0),esk4_0) != k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19]),c_0_20]),c_0_20])])).

cnf(c_0_33,plain,
    ( k1_relset_1(X1,k2_relat_1(X2),X2) = k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0),esk4_0) != k1_relat_1(esk4_0)
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_19]),c_0_20]),c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | k2_relat_1(esk4_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_19]),c_0_20]),c_0_20])]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_19]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:57:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.19/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.029 s
% 0.19/0.53  # Presaturation interreduction done
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.53  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.53  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.53  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.53  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.53  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 0.19/0.53  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.53  fof(c_0_8, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.53  cnf(c_0_9, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.53  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.53  fof(c_0_11, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k1_relat_1(X37),X35)|~r1_tarski(k2_relat_1(X37),X36)|m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.53  cnf(c_0_12, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.53  cnf(c_0_13, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.53  fof(c_0_14, plain, ![X38, X39, X40]:((((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))))&((~v1_funct_2(X40,X38,X39)|X40=k1_xboole_0|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X40!=k1_xboole_0|v1_funct_2(X40,X38,X39)|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.53  fof(c_0_15, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.53  fof(c_0_16, plain, ![X26]:((k1_relat_1(X26)!=k1_xboole_0|X26=k1_xboole_0|~v1_relat_1(X26))&(k2_relat_1(X26)!=k1_xboole_0|X26=k1_xboole_0|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.53  cnf(c_0_17, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10])])).
% 0.19/0.53  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.53  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.53  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.53  cnf(c_0_21, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.53  cnf(c_0_22, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.53  cnf(c_0_23, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.53  cnf(c_0_24, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.53  cnf(c_0_25, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.53  cnf(c_0_26, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20]), c_0_20])])).
% 0.19/0.53  cnf(c_0_27, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)|~r1_tarski(k1_relat_1(X2),X3)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.53  cnf(c_0_28, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~v1_relat_1(X3)|~r1_tarski(k2_relat_1(X3),X2)|~r1_tarski(k1_relat_1(X3),X1)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.19/0.53  cnf(c_0_29, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X2,X3,X1)!=X2|X2!=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X3)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.19/0.53  cnf(c_0_30, plain, (X1=k1_xboole_0|v1_funct_2(X2,X1,X3)|X3!=k1_xboole_0|X2!=k1_xboole_0|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X3)|~r1_tarski(k1_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.19/0.53  cnf(c_0_31, negated_conjecture, (esk4_0=k1_xboole_0|k2_relat_1(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_19])).
% 0.19/0.53  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk4_0)=k1_xboole_0|k1_relset_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0),esk4_0)!=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19]), c_0_20]), c_0_20])])).
% 0.19/0.53  cnf(c_0_33, plain, (k1_relset_1(X1,k2_relat_1(X2),X2)=k1_relat_1(X2)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 0.19/0.53  cnf(c_0_34, negated_conjecture, (k1_relset_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0),esk4_0)!=k1_relat_1(esk4_0)|k1_relat_1(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_29]), c_0_19]), c_0_20]), c_0_20])])).
% 0.19/0.53  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|k2_relat_1(esk4_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_30]), c_0_19]), c_0_20]), c_0_20])]), c_0_31])).
% 0.19/0.53  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19]), c_0_20])])).
% 0.19/0.53  cnf(c_0_37, negated_conjecture, (k1_relat_1(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_19]), c_0_20])])).
% 0.19/0.53  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), c_0_37]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 39
% 0.19/0.53  # Proof object clause steps            : 26
% 0.19/0.53  # Proof object formula steps           : 13
% 0.19/0.53  # Proof object conjectures             : 15
% 0.19/0.53  # Proof object clause conjectures      : 12
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 11
% 0.19/0.53  # Proof object initial formulas used   : 6
% 0.19/0.53  # Proof object generating inferences   : 13
% 0.19/0.53  # Proof object simplifying inferences  : 29
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 19
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 38
% 0.19/0.53  # Removed in clause preprocessing      : 0
% 0.19/0.53  # Initial clauses in saturation        : 38
% 0.19/0.53  # Processed clauses                    : 1288
% 0.19/0.53  # ...of these trivial                  : 16
% 0.19/0.53  # ...subsumed                          : 589
% 0.19/0.53  # ...remaining for further processing  : 683
% 0.19/0.53  # Other redundant clauses eliminated   : 385
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 107
% 0.19/0.53  # Backward-rewritten                   : 37
% 0.19/0.53  # Generated clauses                    : 12575
% 0.19/0.53  # ...of the previous two non-trivial   : 9454
% 0.19/0.53  # Contextual simplify-reflections      : 31
% 0.19/0.53  # Paramodulations                      : 12109
% 0.19/0.53  # Factorizations                       : 35
% 0.19/0.53  # Equation resolutions                 : 431
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 501
% 0.19/0.54  #    Positive orientable unit clauses  : 44
% 0.19/0.54  #    Positive unorientable unit clauses: 3
% 0.19/0.54  #    Negative unit clauses             : 2
% 0.19/0.54  #    Non-unit-clauses                  : 452
% 0.19/0.54  # Current number of unprocessed clauses: 6782
% 0.19/0.54  # ...number of literals in the above   : 28208
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 182
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 17363
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 10669
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 582
% 0.19/0.54  # Unit Clause-clause subsumption calls : 437
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 116
% 0.19/0.54  # BW rewrite match successes           : 44
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 136425
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.186 s
% 0.19/0.54  # System time              : 0.008 s
% 0.19/0.54  # Total time               : 0.194 s
% 0.19/0.54  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
