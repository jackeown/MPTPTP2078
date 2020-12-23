%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t124_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 224 expanded)
%              Number of clauses        :   45 (  96 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 662 expanded)
%              Number of equality atoms :   68 ( 243 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t20_zfmisc_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',redefinition_k6_subset_1)).

fof(t124_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2,X3] : k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t124_funct_1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t117_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',d8_funct_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t3_boole)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t6_boole)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',dt_k6_subset_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',d16_relat_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',dt_o_0_0_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t37_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t3_subset)).

fof(c_0_12,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(k1_tarski(X26),k1_tarski(X27)) != k1_tarski(X26)
        | X26 != X27 )
      & ( X26 = X27
        | k4_xboole_0(k1_tarski(X26),k1_tarski(X27)) = k1_tarski(X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X20,X21] : k6_subset_1(X20,X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2,X3] : k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t124_funct_1])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ r2_hidden(X22,k1_relat_1(X23))
      | k11_relat_1(X23,X22) = k1_tarski(k1_funct_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v2_funct_1(X11)
        | ~ r2_hidden(X12,k1_relat_1(X11))
        | ~ r2_hidden(X13,k1_relat_1(X11))
        | k1_funct_1(X11,X12) != k1_funct_1(X11,X13)
        | X12 = X13
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk2_1(X11),k1_relat_1(X11))
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk3_1(X11),k1_relat_1(X11))
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( k1_funct_1(X11,esk2_1(X11)) = k1_funct_1(X11,esk3_1(X11))
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk2_1(X11) != esk3_1(X11)
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_17,plain,(
    ! [X32] : k4_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_18,plain,(
    ! [X42] :
      ( ~ v1_xboole_0(X42)
      | X42 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X16,X17] : m1_subset_1(k6_subset_1(X16,X17),k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_22,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,negated_conjecture,(
    ! [X5,X6] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & k9_relat_1(esk1_0,k6_subset_1(X5,X6)) = k6_subset_1(k9_relat_1(esk1_0,X5),k9_relat_1(esk1_0,X6))
      & ~ v2_funct_1(esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | k11_relat_1(X9,X10) = k9_relat_1(X9,k1_tarski(X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_25,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_30,plain,(
    ! [X30,X31] :
      ( ( k4_xboole_0(X30,X31) != k1_xboole_0
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | k4_xboole_0(X30,X31) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_31,plain,
    ( X1 != X2
    | k6_subset_1(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( X1 = X2
    | k6_subset_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(esk1_0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k11_relat_1(X1,esk3_1(X1)) = k1_tarski(k1_funct_1(X1,esk3_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( k6_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X33,k1_zfmisc_1(X34))
        | r1_tarski(X33,X34) )
      & ( ~ r1_tarski(X33,X34)
        | m1_subset_1(X33,k1_zfmisc_1(X34)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_42,plain,
    ( k6_subset_1(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( X1 = X2
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k6_subset_1(k9_relat_1(esk1_0,k1_tarski(X1)),k9_relat_1(esk1_0,k1_tarski(X2))) = k9_relat_1(esk1_0,k1_tarski(X1))
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_45,plain,
    ( k9_relat_1(X1,k1_tarski(esk3_1(X1))) = k1_tarski(k1_funct_1(X1,esk3_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,plain,
    ( k11_relat_1(X1,esk2_1(X1)) = k1_tarski(k1_funct_1(X1,esk2_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_50,plain,
    ( k6_subset_1(X1,o_0_0_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,plain,
    ( k6_subset_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(k1_tarski(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k6_subset_1(k9_relat_1(esk1_0,k1_tarski(X1)),k1_tarski(k1_funct_1(esk1_0,esk3_1(esk1_0)))) = k9_relat_1(esk1_0,k1_tarski(X1))
    | X1 = esk3_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_55,plain,
    ( k1_funct_1(X1,esk2_1(X1)) = k1_funct_1(X1,esk3_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,plain,
    ( k9_relat_1(X1,k1_tarski(esk2_1(X1))) = k1_tarski(k1_funct_1(X1,esk2_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_49])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_50])).

cnf(c_0_58,plain,
    ( k6_subset_1(X1,X2) = o_0_0_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( v2_funct_1(X1)
    | esk2_1(X1) != esk3_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( k6_subset_1(k9_relat_1(esk1_0,k1_tarski(X1)),k1_tarski(k1_funct_1(esk1_0,esk2_1(esk1_0)))) = k9_relat_1(esk1_0,k1_tarski(X1))
    | X1 = esk3_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k6_subset_1(k9_relat_1(esk1_0,k1_tarski(X1)),k1_tarski(k1_funct_1(esk1_0,esk2_1(esk1_0)))) = k9_relat_1(esk1_0,k1_tarski(X1))
    | X1 = esk2_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_56]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_64,plain,
    ( k6_subset_1(k1_tarski(X1),k1_tarski(X1)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k6_subset_1(k9_relat_1(esk1_0,k1_tarski(X1)),k1_tarski(k1_funct_1(esk1_0,esk2_1(esk1_0)))) = k9_relat_1(esk1_0,k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_46]),c_0_47])]),c_0_48]),c_0_62])).

cnf(c_0_66,plain,
    ( k6_subset_1(X1,X1) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_63])).

cnf(c_0_67,plain,
    ( k1_tarski(X1) != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_56]),c_0_66]),c_0_46]),c_0_47])]),c_0_67]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
