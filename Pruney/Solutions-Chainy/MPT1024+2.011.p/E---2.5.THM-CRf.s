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
% DateTime   : Thu Dec  3 11:06:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 148 expanded)
%              Number of clauses        :   27 (  61 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 608 expanded)
%              Number of equality atoms :   13 (  73 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_10,plain,(
    ! [X83,X84,X85,X86] :
      ( ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X83,X84)))
      | k7_relset_1(X83,X84,X85,X86) = k9_relat_1(X85,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ! [X108] :
      ( v1_funct_1(esk10_0)
      & v1_funct_2(esk10_0,esk7_0,esk8_0)
      & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
      & r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0))
      & ( ~ r2_hidden(X108,esk7_0)
        | ~ r2_hidden(X108,esk9_0)
        | esk11_0 != k1_funct_1(esk10_0,X108) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X71,X72,X73] :
      ( ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))
      | v1_relat_1(X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | m1_subset_1(X40,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X49,X50,X51,X53] :
      ( ( r2_hidden(esk4_3(X49,X50,X51),k1_relat_1(X51))
        | ~ r2_hidden(X49,k9_relat_1(X51,X50))
        | ~ v1_relat_1(X51) )
      & ( r2_hidden(k4_tarski(esk4_3(X49,X50,X51),X49),X51)
        | ~ r2_hidden(X49,k9_relat_1(X51,X50))
        | ~ v1_relat_1(X51) )
      & ( r2_hidden(esk4_3(X49,X50,X51),X50)
        | ~ r2_hidden(X49,k9_relat_1(X51,X50))
        | ~ v1_relat_1(X51) )
      & ( ~ r2_hidden(X53,k1_relat_1(X51))
        | ~ r2_hidden(k4_tarski(X53,X49),X51)
        | ~ r2_hidden(X53,X50)
        | r2_hidden(X49,k9_relat_1(X51,X50))
        | ~ v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k7_relset_1(esk7_0,esk8_0,esk10_0,X1) = k9_relat_1(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk11_0,k9_relat_1(esk10_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_13])).

fof(c_0_24,plain,(
    ! [X67,X68,X69] :
      ( ( r2_hidden(X67,k1_relat_1(X69))
        | ~ r2_hidden(k4_tarski(X67,X68),X69)
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( X68 = k1_funct_1(X69,X67)
        | ~ r2_hidden(k4_tarski(X67,X68),X69)
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( ~ r2_hidden(X67,k1_relat_1(X69))
        | X68 != k1_funct_1(X69,X67)
        | r2_hidden(k4_tarski(X67,X68),X69)
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_25,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk11_0,esk9_0,esk10_0),esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_32,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk4_3(esk11_0,esk9_0,esk10_0),esk11_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0)
    | esk11_0 != k1_funct_1(esk10_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk10_0,esk4_3(esk11_0,esk9_0,esk10_0)) = esk11_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_29]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_3(esk11_0,esk9_0,esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_23])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk11_0,esk9_0,esk10_0),esk11_0),k2_zfmisc_1(esk7_0,esk8_0))
    | v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk11_0,esk9_0,esk10_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.20/0.49  # and selection function SelectNewComplexAHPNS.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.030 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 0.20/0.49  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.49  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.49  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.20/0.49  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.49  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.49  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.49  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.20/0.49  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.20/0.49  fof(c_0_10, plain, ![X83, X84, X85, X86]:(~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X83,X84)))|k7_relset_1(X83,X84,X85,X86)=k9_relat_1(X85,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.49  fof(c_0_11, negated_conjecture, ![X108]:(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,esk8_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&(r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0))&(~r2_hidden(X108,esk7_0)|~r2_hidden(X108,esk9_0)|esk11_0!=k1_funct_1(esk10_0,X108)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.20/0.49  cnf(c_0_12, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.49  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.49  fof(c_0_14, plain, ![X71, X72, X73]:(~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))|v1_relat_1(X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.49  fof(c_0_15, plain, ![X40, X41, X42]:(~r2_hidden(X40,X41)|~m1_subset_1(X41,k1_zfmisc_1(X42))|m1_subset_1(X40,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.49  fof(c_0_16, plain, ![X49, X50, X51, X53]:((((r2_hidden(esk4_3(X49,X50,X51),k1_relat_1(X51))|~r2_hidden(X49,k9_relat_1(X51,X50))|~v1_relat_1(X51))&(r2_hidden(k4_tarski(esk4_3(X49,X50,X51),X49),X51)|~r2_hidden(X49,k9_relat_1(X51,X50))|~v1_relat_1(X51)))&(r2_hidden(esk4_3(X49,X50,X51),X50)|~r2_hidden(X49,k9_relat_1(X51,X50))|~v1_relat_1(X51)))&(~r2_hidden(X53,k1_relat_1(X51))|~r2_hidden(k4_tarski(X53,X49),X51)|~r2_hidden(X53,X50)|r2_hidden(X49,k9_relat_1(X51,X50))|~v1_relat_1(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.20/0.49  cnf(c_0_17, negated_conjecture, (r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.49  cnf(c_0_18, negated_conjecture, (k7_relset_1(esk7_0,esk8_0,esk10_0,X1)=k9_relat_1(esk10_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.49  cnf(c_0_19, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.49  cnf(c_0_20, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_22, negated_conjecture, (r2_hidden(esk11_0,k9_relat_1(esk10_0,esk9_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.49  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_19, c_0_13])).
% 0.20/0.49  fof(c_0_24, plain, ![X67, X68, X69]:(((r2_hidden(X67,k1_relat_1(X69))|~r2_hidden(k4_tarski(X67,X68),X69)|(~v1_relat_1(X69)|~v1_funct_1(X69)))&(X68=k1_funct_1(X69,X67)|~r2_hidden(k4_tarski(X67,X68),X69)|(~v1_relat_1(X69)|~v1_funct_1(X69))))&(~r2_hidden(X67,k1_relat_1(X69))|X68!=k1_funct_1(X69,X67)|r2_hidden(k4_tarski(X67,X68),X69)|(~v1_relat_1(X69)|~v1_funct_1(X69)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.49  fof(c_0_25, plain, ![X38, X39]:(~m1_subset_1(X38,X39)|(v1_xboole_0(X39)|r2_hidden(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.49  cnf(c_0_26, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(esk7_0,esk8_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 0.20/0.49  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk11_0,esk9_0,esk10_0),esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.20/0.49  cnf(c_0_28, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.49  cnf(c_0_30, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  fof(c_0_31, plain, ![X43, X44, X45]:(~r2_hidden(X43,X44)|~m1_subset_1(X44,k1_zfmisc_1(X45))|~v1_xboole_0(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.49  fof(c_0_32, plain, ![X20, X21, X22, X23]:(((r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))&(r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23))))&(~r2_hidden(X20,X22)|~r2_hidden(X21,X23)|r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 0.20/0.49  cnf(c_0_33, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.49  cnf(c_0_34, negated_conjecture, (m1_subset_1(k4_tarski(esk4_3(esk11_0,esk9_0,esk10_0),esk11_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.49  cnf(c_0_35, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk9_0)|esk11_0!=k1_funct_1(esk10_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.49  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk10_0,esk4_3(esk11_0,esk9_0,esk10_0))=esk11_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_29]), c_0_23])])).
% 0.20/0.49  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_3(esk11_0,esk9_0,esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_23])])).
% 0.20/0.49  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.49  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.49  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk11_0,esk9_0,esk10_0),esk11_0),k2_zfmisc_1(esk7_0,esk8_0))|v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.49  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk4_3(esk11_0,esk9_0,esk10_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.20/0.49  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk10_0)|~v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_38, c_0_13])).
% 0.20/0.49  cnf(c_0_43, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.49  cnf(c_0_44, negated_conjecture, (~r2_hidden(X1,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.20/0.49  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_27, c_0_44]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 46
% 0.20/0.49  # Proof object clause steps            : 27
% 0.20/0.49  # Proof object formula steps           : 19
% 0.20/0.49  # Proof object conjectures             : 21
% 0.20/0.49  # Proof object clause conjectures      : 18
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 13
% 0.20/0.49  # Proof object initial formulas used   : 9
% 0.20/0.49  # Proof object generating inferences   : 11
% 0.20/0.49  # Proof object simplifying inferences  : 14
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 40
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 73
% 0.20/0.49  # Removed in clause preprocessing      : 4
% 0.20/0.49  # Initial clauses in saturation        : 69
% 0.20/0.49  # Processed clauses                    : 1403
% 0.20/0.49  # ...of these trivial                  : 22
% 0.20/0.49  # ...subsumed                          : 736
% 0.20/0.49  # ...remaining for further processing  : 645
% 0.20/0.49  # Other redundant clauses eliminated   : 4
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 7
% 0.20/0.49  # Backward-rewritten                   : 52
% 0.20/0.49  # Generated clauses                    : 4755
% 0.20/0.49  # ...of the previous two non-trivial   : 3840
% 0.20/0.49  # Contextual simplify-reflections      : 1
% 0.20/0.49  # Paramodulations                      : 4747
% 0.20/0.49  # Factorizations                       : 0
% 0.20/0.49  # Equation resolutions                 : 4
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 510
% 0.20/0.49  #    Positive orientable unit clauses  : 101
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 22
% 0.20/0.49  #    Non-unit-clauses                  : 387
% 0.20/0.49  # Current number of unprocessed clauses: 2531
% 0.20/0.49  # ...number of literals in the above   : 9431
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 134
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 21146
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 9004
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 236
% 0.20/0.49  # Unit Clause-clause subsumption calls : 509
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 35
% 0.20/0.49  # BW rewrite match successes           : 11
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 91222
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.142 s
% 0.20/0.49  # System time              : 0.006 s
% 0.20/0.49  # Total time               : 0.148 s
% 0.20/0.49  # Maximum resident set size: 1632 pages
%------------------------------------------------------------------------------
