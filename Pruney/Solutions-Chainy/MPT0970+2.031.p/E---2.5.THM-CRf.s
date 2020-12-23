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
% DateTime   : Thu Dec  3 11:01:31 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 406 expanded)
%              Number of clauses        :   66 ( 184 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   27
%              Number of atoms          :  314 (1563 expanded)
%              Number of equality atoms :  111 ( 458 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_14,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ r1_tarski(X44,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_15,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X24),X22)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X27,X26),X22)
        | r2_hidden(X26,X23)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(esk3_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(X31,esk3_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) )
      & ( r2_hidden(esk3_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk4_2(X28,X29),esk3_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( X1 != k2_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_23,plain,
    ( X1 != k2_relat_1(k2_relat_1(k1_xboole_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_25,plain,
    ( X1 != k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_27,plain,(
    ! [X6,X7] :
      ( ( ~ r2_hidden(esk1_2(X6,X7),X6)
        | ~ r2_hidden(esk1_2(X6,X7),X7)
        | X6 = X7 )
      & ( r2_hidden(esk1_2(X6,X7),X6)
        | r2_hidden(esk1_2(X6,X7),X7)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_28,plain,
    ( X1 != k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_32,plain,
    ( X1 != k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_33,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

cnf(c_0_35,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

fof(c_0_36,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_relset_1(X48,X49,X50) = k1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_37,plain,(
    ! [X54,X55,X56] :
      ( ( ~ v1_funct_2(X56,X54,X55)
        | X54 = k1_relset_1(X54,X55,X56)
        | X55 = k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_relset_1(X54,X55,X56)
        | v1_funct_2(X56,X54,X55)
        | X55 = k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( ~ v1_funct_2(X56,X54,X55)
        | X54 = k1_relset_1(X54,X55,X56)
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_relset_1(X54,X55,X56)
        | v1_funct_2(X56,X54,X55)
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( ~ v1_funct_2(X56,X54,X55)
        | X56 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X56 != k1_xboole_0
        | v1_funct_2(X56,X54,X55)
        | X54 = k1_xboole_0
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_38,negated_conjecture,(
    ! [X60] :
      ( v1_funct_1(esk10_0)
      & v1_funct_2(esk10_0,esk8_0,esk9_0)
      & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
      & ( r2_hidden(esk11_1(X60),esk8_0)
        | ~ r2_hidden(X60,esk9_0) )
      & ( X60 = k1_funct_1(esk10_0,esk11_1(X60))
        | ~ r2_hidden(X60,esk9_0) )
      & k2_relset_1(esk8_0,esk9_0,esk10_0) != esk9_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])])])).

fof(c_0_39,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k2_relset_1(X51,X52,X53) = k2_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_40,plain,
    ( X1 != k2_relat_1(X2)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_41,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k2_relset_1(esk8_0,esk9_0,esk10_0) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k1_xboole_0 = X1
    | X1 != k2_relat_1(X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_47,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(esk10_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_51,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_52,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | v1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_53,plain,(
    ! [X33,X34,X35,X37,X38,X39,X41] :
      ( ( r2_hidden(esk5_3(X33,X34,X35),k1_relat_1(X33))
        | ~ r2_hidden(X35,X34)
        | X34 != k2_relat_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( X35 = k1_funct_1(X33,esk5_3(X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k2_relat_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(X38,k1_relat_1(X33))
        | X37 != k1_funct_1(X33,X38)
        | r2_hidden(X37,X34)
        | X34 != k2_relat_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(esk6_2(X33,X39),X39)
        | ~ r2_hidden(X41,k1_relat_1(X33))
        | esk6_2(X33,X39) != k1_funct_1(X33,X41)
        | X39 = k2_relat_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(esk7_2(X33,X39),k1_relat_1(X33))
        | r2_hidden(esk6_2(X33,X39),X39)
        | X39 = k2_relat_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( esk6_2(X33,X39) = k1_funct_1(X33,esk7_2(X33,X39))
        | r2_hidden(esk6_2(X33,X39),X39)
        | X39 = k2_relat_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k1_relat_1(esk10_0)
    | esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_45])])).

cnf(c_0_56,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | esk10_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk10_0) = k1_xboole_0
    | esk9_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

fof(c_0_62,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_63,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_64,negated_conjecture,
    ( X1 != k2_relat_1(esk10_0)
    | esk9_0 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])]),c_0_19])).

fof(c_0_65,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(er,[status(thm)],[c_0_64])).

fof(c_0_69,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r2_hidden(X10,X12)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) )
      & ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) )
      & ( ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X11,X13)
        | r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_45])).

cnf(c_0_73,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( k2_relat_1(esk10_0) = k1_xboole_0
    | esk9_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_31])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_77,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k1_funct_1(esk10_0,esk11_1(X1))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk11_1(X1),esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_84,negated_conjecture,
    ( esk8_0 = k1_relat_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_48]),c_0_45])]),c_0_78])).

cnf(c_0_85,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk3_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_86,negated_conjecture,
    ( X1 = k2_relat_1(esk10_0)
    | r2_hidden(esk3_2(esk10_0,X1),esk9_0)
    | r2_hidden(esk3_2(esk10_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk10_0)
    | ~ r2_hidden(esk11_1(X1),k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_60])])]),c_0_61])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk11_1(X1),k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,plain,
    ( X1 = k2_relat_1(X2)
    | X3 != k2_relat_1(X2)
    | ~ r2_hidden(esk3_2(X2,X1),X1)
    | ~ r2_hidden(esk3_2(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_85,c_0_20])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_2(esk10_0,esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_86]),c_0_50])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk10_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( X1 != k2_relat_1(esk10_0)
    | ~ r2_hidden(esk3_2(esk10_0,esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_50])).

cnf(c_0_93,negated_conjecture,
    ( X1 != k2_relat_1(esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_90]),c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(er,[status(thm)],[c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:23:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.40  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.40  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 0.19/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.40  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.40  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.40  fof(c_0_14, plain, ![X43, X44]:(~r2_hidden(X43,X44)|~r1_tarski(X44,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.40  fof(c_0_15, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.40  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_17, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  fof(c_0_18, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X24),X22)|X23!=k2_relat_1(X22))&(~r2_hidden(k4_tarski(X27,X26),X22)|r2_hidden(X26,X23)|X23!=k2_relat_1(X22)))&((~r2_hidden(esk3_2(X28,X29),X29)|~r2_hidden(k4_tarski(X31,esk3_2(X28,X29)),X28)|X29=k2_relat_1(X28))&(r2_hidden(esk3_2(X28,X29),X29)|r2_hidden(k4_tarski(esk4_2(X28,X29),esk3_2(X28,X29)),X28)|X29=k2_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.40  cnf(c_0_19, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_21, plain, (X1!=k2_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  cnf(c_0_22, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_23, plain, (X1!=k2_relat_1(k2_relat_1(k1_xboole_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.40  cnf(c_0_24, plain, (~r2_hidden(X1,k2_relat_1(k2_relat_1(k1_xboole_0)))), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_25, plain, (X1!=k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.19/0.40  cnf(c_0_26, plain, (~r2_hidden(X1,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.40  fof(c_0_27, plain, ![X6, X7]:((~r2_hidden(esk1_2(X6,X7),X6)|~r2_hidden(esk1_2(X6,X7),X7)|X6=X7)&(r2_hidden(esk1_2(X6,X7),X6)|r2_hidden(esk1_2(X6,X7),X7)|X6=X7)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.40  cnf(c_0_28, plain, (X1!=k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.19/0.40  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_30, plain, (~r2_hidden(X1,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_31, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.19/0.40  cnf(c_0_32, plain, (X1!=k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.19/0.40  cnf(c_0_33, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.19/0.40  fof(c_0_34, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.19/0.40  cnf(c_0_35, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.19/0.40  fof(c_0_36, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_relset_1(X48,X49,X50)=k1_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.40  fof(c_0_37, plain, ![X54, X55, X56]:((((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&((~v1_funct_2(X56,X54,X55)|X56=k1_xboole_0|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X56!=k1_xboole_0|v1_funct_2(X56,X54,X55)|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.40  fof(c_0_38, negated_conjecture, ![X60]:(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk8_0,esk9_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&(((r2_hidden(esk11_1(X60),esk8_0)|~r2_hidden(X60,esk9_0))&(X60=k1_funct_1(esk10_0,esk11_1(X60))|~r2_hidden(X60,esk9_0)))&k2_relset_1(esk8_0,esk9_0,esk10_0)!=esk9_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])])])).
% 0.19/0.40  fof(c_0_39, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k2_relset_1(X51,X52,X53)=k2_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.40  cnf(c_0_40, plain, (X1!=k2_relat_1(X2)|X2!=k1_xboole_0|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.19/0.40  cnf(c_0_41, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  cnf(c_0_42, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (k2_relset_1(esk8_0,esk9_0,esk10_0)!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_44, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_46, plain, (k1_xboole_0=X1|X1!=k2_relat_1(X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.19/0.40  cnf(c_0_47, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (k2_relat_1(esk10_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.19/0.40  cnf(c_0_51, plain, (k2_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.40  fof(c_0_52, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|v1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.40  fof(c_0_53, plain, ![X33, X34, X35, X37, X38, X39, X41]:((((r2_hidden(esk5_3(X33,X34,X35),k1_relat_1(X33))|~r2_hidden(X35,X34)|X34!=k2_relat_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(X35=k1_funct_1(X33,esk5_3(X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k2_relat_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(~r2_hidden(X38,k1_relat_1(X33))|X37!=k1_funct_1(X33,X38)|r2_hidden(X37,X34)|X34!=k2_relat_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&((~r2_hidden(esk6_2(X33,X39),X39)|(~r2_hidden(X41,k1_relat_1(X33))|esk6_2(X33,X39)!=k1_funct_1(X33,X41))|X39=k2_relat_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&((r2_hidden(esk7_2(X33,X39),k1_relat_1(X33))|r2_hidden(esk6_2(X33,X39),X39)|X39=k2_relat_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(esk6_2(X33,X39)=k1_funct_1(X33,esk7_2(X33,X39))|r2_hidden(esk6_2(X33,X39),X39)|X39=k2_relat_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (esk8_0=k1_relat_1(esk10_0)|esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_45])])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (esk10_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_45])])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (esk9_0!=k1_xboole_0|esk10_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  cnf(c_0_57, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.40  cnf(c_0_58, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (k1_relat_1(esk10_0)=k1_xboole_0|esk9_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 0.19/0.40  fof(c_0_62, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.40  fof(c_0_63, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (X1!=k2_relat_1(esk10_0)|esk9_0!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61])]), c_0_19])).
% 0.19/0.40  fof(c_0_65, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.40  cnf(c_0_66, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.40  cnf(c_0_67, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (esk9_0!=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(er,[status(thm)],[c_0_64])).
% 0.19/0.40  fof(c_0_69, plain, ![X10, X11, X12, X13]:(((r2_hidden(X10,X12)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)))&(r2_hidden(X11,X13)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13))))&(~r2_hidden(X10,X12)|~r2_hidden(X11,X13)|r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.40  cnf(c_0_70, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_66, c_0_45])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_67, c_0_45])).
% 0.19/0.40  cnf(c_0_73, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k2_relat_1(esk10_0)=k1_xboole_0|esk9_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_31])).
% 0.19/0.40  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(X1,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.19/0.40  cnf(c_0_77, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_73])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (esk9_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_74])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(k4_tarski(X2,X1),esk10_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.40  cnf(c_0_80, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_81, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (X1=k1_funct_1(esk10_0,esk11_1(X1))|~r2_hidden(X1,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (r2_hidden(esk11_1(X1),esk8_0)|~r2_hidden(X1,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (esk8_0=k1_relat_1(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_48]), c_0_45])]), c_0_78])).
% 0.19/0.40  cnf(c_0_85, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk3_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (X1=k2_relat_1(esk10_0)|r2_hidden(esk3_2(esk10_0,X1),esk9_0)|r2_hidden(esk3_2(esk10_0,X1),X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (r2_hidden(X1,X2)|X2!=k2_relat_1(esk10_0)|~r2_hidden(esk11_1(X1),k1_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_60])])]), c_0_61])])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (r2_hidden(esk11_1(X1),k1_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.40  cnf(c_0_89, plain, (X1=k2_relat_1(X2)|X3!=k2_relat_1(X2)|~r2_hidden(esk3_2(X2,X1),X1)|~r2_hidden(esk3_2(X2,X1),X3)), inference(spm,[status(thm)],[c_0_85, c_0_20])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (r2_hidden(esk3_2(esk10_0,esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_86]), c_0_50])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (r2_hidden(X1,X2)|X2!=k2_relat_1(esk10_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (X1!=k2_relat_1(esk10_0)|~r2_hidden(esk3_2(esk10_0,esk9_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_50])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (X1!=k2_relat_1(esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_90]), c_0_92])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, ($false), inference(er,[status(thm)],[c_0_93]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 95
% 0.19/0.40  # Proof object clause steps            : 66
% 0.19/0.40  # Proof object formula steps           : 29
% 0.19/0.40  # Proof object conjectures             : 32
% 0.19/0.40  # Proof object clause conjectures      : 29
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 24
% 0.19/0.40  # Proof object initial formulas used   : 14
% 0.19/0.40  # Proof object generating inferences   : 40
% 0.19/0.40  # Proof object simplifying inferences  : 29
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 14
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 35
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 35
% 0.19/0.40  # Processed clauses                    : 641
% 0.19/0.40  # ...of these trivial                  : 14
% 0.19/0.40  # ...subsumed                          : 370
% 0.19/0.40  # ...remaining for further processing  : 257
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 18
% 0.19/0.40  # Backward-rewritten                   : 29
% 0.19/0.40  # Generated clauses                    : 1230
% 0.19/0.40  # ...of the previous two non-trivial   : 1202
% 0.19/0.40  # Contextual simplify-reflections      : 6
% 0.19/0.40  # Paramodulations                      : 1179
% 0.19/0.40  # Factorizations                       : 10
% 0.19/0.40  # Equation resolutions                 : 37
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 171
% 0.19/0.40  #    Positive orientable unit clauses  : 17
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 9
% 0.19/0.40  #    Non-unit-clauses                  : 145
% 0.19/0.40  # Current number of unprocessed clauses: 535
% 0.19/0.40  # ...number of literals in the above   : 2437
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 86
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3219
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1609
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 168
% 0.19/0.40  # Unit Clause-clause subsumption calls : 211
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 4
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 15012
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.059 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.066 s
% 0.19/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
