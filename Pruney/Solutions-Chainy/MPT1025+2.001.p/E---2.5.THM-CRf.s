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
% DateTime   : Thu Dec  3 11:06:35 EST 2020

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 231 expanded)
%              Number of clauses        :   59 ( 104 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  287 ( 888 expanded)
%              Number of equality atoms :   64 ( 137 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X31,X32,X33,X35] :
      ( ( r2_hidden(esk5_3(X31,X32,X33),k1_relat_1(X33))
        | ~ r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(esk5_3(X31,X32,X33),X31),X33)
        | ~ r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X32)
        | ~ r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(X35,k1_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X35,X31),X33)
        | ~ r2_hidden(X35,X32)
        | r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_19,plain,(
    ! [X30] :
      ( ~ v1_xboole_0(X30)
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | X11 = X12
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k9_relat_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_30,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(X15,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(esk3_2(X19,X20),X22)
        | ~ r2_hidden(X22,X19)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_31,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_33,plain,(
    ! [X49,X50,X51] :
      ( ( r2_hidden(k1_mcart_1(X49),X50)
        | ~ r2_hidden(X49,k2_zfmisc_1(X50,X51)) )
      & ( r2_hidden(k2_mcart_1(X49),X51)
        | ~ r2_hidden(X49,k2_zfmisc_1(X50,X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

cnf(c_0_39,plain,
    ( r2_hidden(k2_mcart_1(esk1_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

fof(c_0_41,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k7_relset_1(X45,X46,X47,X48) = k9_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_42,negated_conjecture,(
    ! [X60] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))
      & ( ~ m1_subset_1(X60,esk6_0)
        | ~ r2_hidden(X60,esk8_0)
        | esk10_0 != k1_funct_1(esk9_0,X60) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])])).

fof(c_0_43,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k1_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( X37 = k1_funct_1(X38,X36)
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( ~ r2_hidden(X36,k1_relat_1(X38))
        | X37 != k1_funct_1(X38,X36)
        | r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_44,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_45,plain,(
    ! [X52,X53,X54] :
      ( ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X54 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != k1_xboole_0
        | v1_funct_2(X54,X52,X53)
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_46,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_relset_1(X42,X43,X44) = k1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_48,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_39])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_51,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_55,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | m1_subset_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_56,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

fof(c_0_62,plain,(
    ! [X24] : k3_tarski(k1_zfmisc_1(X24)) = X24 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_64,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_50])).

fof(c_0_65,plain,(
    ! [X25] : ~ v1_xboole_0(k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( k7_relset_1(esk6_0,esk7_0,esk9_0,X1) = k9_relat_1(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | esk10_0 != k1_funct_1(esk9_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_69,plain,
    ( k1_funct_1(X1,esk5_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_52])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_73,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_57])])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_52])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_78,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_25])])).

cnf(c_0_80,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(esk5_3(esk10_0,X1,esk9_0),esk6_0)
    | ~ r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk8_0)
    | ~ r2_hidden(esk10_0,k9_relat_1(esk9_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])])])).

cnf(c_0_83,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( ~ m1_subset_1(esk5_3(esk10_0,esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_81]),c_0_71])])).

cnf(c_0_89,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk5_3(X1,X2,esk9_0),esk6_0)
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_71])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_27]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_81])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.20/1.42  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 1.20/1.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.20/1.42  #
% 1.20/1.42  # Preprocessing time       : 0.028 s
% 1.20/1.42  
% 1.20/1.42  # Proof found!
% 1.20/1.42  # SZS status Theorem
% 1.20/1.42  # SZS output start CNFRefutation
% 1.20/1.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.20/1.42  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.20/1.42  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.20/1.42  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.20/1.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.20/1.42  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 1.20/1.42  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.20/1.42  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 1.20/1.42  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.20/1.42  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.20/1.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.20/1.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.20/1.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.20/1.42  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.20/1.42  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.20/1.42  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.20/1.42  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.20/1.42  fof(c_0_17, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.20/1.42  fof(c_0_18, plain, ![X31, X32, X33, X35]:((((r2_hidden(esk5_3(X31,X32,X33),k1_relat_1(X33))|~r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33))&(r2_hidden(k4_tarski(esk5_3(X31,X32,X33),X31),X33)|~r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33)))&(r2_hidden(esk5_3(X31,X32,X33),X32)|~r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33)))&(~r2_hidden(X35,k1_relat_1(X33))|~r2_hidden(k4_tarski(X35,X31),X33)|~r2_hidden(X35,X32)|r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 1.20/1.42  fof(c_0_19, plain, ![X30]:(~v1_xboole_0(X30)|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 1.20/1.42  fof(c_0_20, plain, ![X11, X12]:(~v1_xboole_0(X11)|X11=X12|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 1.20/1.42  cnf(c_0_21, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.20/1.42  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.20/1.42  cnf(c_0_23, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.20/1.42  cnf(c_0_24, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.20/1.42  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.20/1.42  cnf(c_0_26, plain, (~r2_hidden(X1,k9_relat_1(X2,X3))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 1.20/1.42  cnf(c_0_27, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.20/1.42  cnf(c_0_28, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.20/1.42  cnf(c_0_29, plain, (v1_xboole_0(k9_relat_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.20/1.42  fof(c_0_30, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.20/1.42  cnf(c_0_31, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.20/1.42  cnf(c_0_32, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.20/1.42  fof(c_0_33, plain, ![X49, X50, X51]:((r2_hidden(k1_mcart_1(X49),X50)|~r2_hidden(X49,k2_zfmisc_1(X50,X51)))&(r2_hidden(k2_mcart_1(X49),X51)|~r2_hidden(X49,k2_zfmisc_1(X50,X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 1.20/1.42  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 1.20/1.42  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_32])).
% 1.20/1.42  cnf(c_0_36, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.20/1.42  cnf(c_0_37, plain, (~r2_hidden(X1,k3_tarski(k1_xboole_0))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.20/1.42  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 1.20/1.42  cnf(c_0_39, plain, (r2_hidden(k2_mcart_1(esk1_1(k2_zfmisc_1(X1,X2))),X2)|v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 1.20/1.42  cnf(c_0_40, plain, (v1_xboole_0(k3_tarski(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 1.20/1.42  fof(c_0_41, plain, ![X45, X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k7_relset_1(X45,X46,X47,X48)=k9_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 1.20/1.42  fof(c_0_42, negated_conjecture, ![X60]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))&(~m1_subset_1(X60,esk6_0)|(~r2_hidden(X60,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X60))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])])).
% 1.20/1.42  fof(c_0_43, plain, ![X36, X37, X38]:(((r2_hidden(X36,k1_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(X37=k1_funct_1(X38,X36)|~r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38))))&(~r2_hidden(X36,k1_relat_1(X38))|X37!=k1_funct_1(X38,X36)|r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 1.20/1.42  fof(c_0_44, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.20/1.42  fof(c_0_45, plain, ![X52, X53, X54]:((((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))))&((~v1_funct_2(X54,X52,X53)|X54=k1_xboole_0|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X54!=k1_xboole_0|v1_funct_2(X54,X52,X53)|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.20/1.42  fof(c_0_46, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_relset_1(X42,X43,X44)=k1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.20/1.42  cnf(c_0_47, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.20/1.42  fof(c_0_48, plain, ![X28, X29]:(~m1_subset_1(X28,X29)|(v1_xboole_0(X29)|r2_hidden(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 1.20/1.42  cnf(c_0_49, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_21, c_0_39])).
% 1.20/1.42  cnf(c_0_50, plain, (v1_xboole_0(k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 1.20/1.42  cnf(c_0_51, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.20/1.42  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.20/1.42  cnf(c_0_53, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.20/1.42  cnf(c_0_54, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.20/1.42  fof(c_0_55, plain, ![X26, X27]:(~r2_hidden(X26,X27)|m1_subset_1(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 1.20/1.42  cnf(c_0_56, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.20/1.42  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.20/1.42  cnf(c_0_58, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.20/1.42  cnf(c_0_59, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_47])).
% 1.20/1.42  cnf(c_0_60, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.20/1.42  cnf(c_0_61, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_28, c_0_49])).
% 1.20/1.42  fof(c_0_62, plain, ![X24]:k3_tarski(k1_zfmisc_1(X24))=X24, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 1.20/1.42  cnf(c_0_63, plain, (~r2_hidden(X1,k3_tarski(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 1.20/1.42  cnf(c_0_64, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_50])).
% 1.20/1.42  fof(c_0_65, plain, ![X25]:~v1_xboole_0(k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.20/1.42  cnf(c_0_66, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.20/1.42  cnf(c_0_67, negated_conjecture, (k7_relset_1(esk6_0,esk7_0,esk9_0,X1)=k9_relat_1(esk9_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.20/1.42  cnf(c_0_68, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(X1,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.20/1.42  cnf(c_0_69, plain, (k1_funct_1(X1,esk5_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_53, c_0_22])).
% 1.20/1.42  cnf(c_0_70, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.20/1.42  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_52])).
% 1.20/1.42  cnf(c_0_72, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.20/1.42  cnf(c_0_73, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.20/1.42  cnf(c_0_74, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_52]), c_0_57])])).
% 1.20/1.42  cnf(c_0_75, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_58, c_0_52])).
% 1.20/1.42  cnf(c_0_76, plain, (r2_hidden(X1,k3_tarski(X2))|v1_xboole_0(X2)|~m1_subset_1(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.20/1.42  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_61])).
% 1.20/1.42  cnf(c_0_78, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.20/1.42  cnf(c_0_79, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_25])])).
% 1.20/1.42  cnf(c_0_80, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.20/1.42  cnf(c_0_81, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 1.20/1.42  cnf(c_0_82, negated_conjecture, (~m1_subset_1(esk5_3(esk10_0,X1,esk9_0),esk6_0)|~r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk8_0)|~r2_hidden(esk10_0,k9_relat_1(esk9_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])])])).
% 1.20/1.42  cnf(c_0_83, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.20/1.42  cnf(c_0_84, plain, (m1_subset_1(esk5_3(X1,X2,X3),k1_relat_1(X3))|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.20/1.42  cnf(c_0_85, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.20/1.42  cnf(c_0_86, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_79]), c_0_80])).
% 1.20/1.42  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_26, c_0_81])).
% 1.20/1.42  cnf(c_0_88, negated_conjecture, (~m1_subset_1(esk5_3(esk10_0,esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_81]), c_0_71])])).
% 1.20/1.42  cnf(c_0_89, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk5_3(X1,X2,esk9_0),esk6_0)|~r2_hidden(X1,k9_relat_1(esk9_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_71])])).
% 1.20/1.42  cnf(c_0_90, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_27]), c_0_87])).
% 1.20/1.42  cnf(c_0_91, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_81])])).
% 1.20/1.42  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91]), c_0_25])]), ['proof']).
% 1.20/1.42  # SZS output end CNFRefutation
% 1.20/1.42  # Proof object total steps             : 93
% 1.20/1.42  # Proof object clause steps            : 59
% 1.20/1.42  # Proof object formula steps           : 34
% 1.20/1.42  # Proof object conjectures             : 23
% 1.20/1.42  # Proof object clause conjectures      : 20
% 1.20/1.42  # Proof object formula conjectures     : 3
% 1.20/1.42  # Proof object initial clauses used    : 25
% 1.20/1.42  # Proof object initial formulas used   : 17
% 1.20/1.42  # Proof object generating inferences   : 30
% 1.20/1.42  # Proof object simplifying inferences  : 26
% 1.20/1.42  # Training examples: 0 positive, 0 negative
% 1.20/1.42  # Parsed axioms                        : 17
% 1.20/1.42  # Removed by relevancy pruning/SinE    : 0
% 1.20/1.42  # Initial clauses                      : 38
% 1.20/1.42  # Removed in clause preprocessing      : 0
% 1.20/1.42  # Initial clauses in saturation        : 38
% 1.20/1.42  # Processed clauses                    : 8829
% 1.20/1.42  # ...of these trivial                  : 6
% 1.20/1.42  # ...subsumed                          : 7693
% 1.20/1.42  # ...remaining for further processing  : 1130
% 1.20/1.42  # Other redundant clauses eliminated   : 47
% 1.20/1.42  # Clauses deleted for lack of memory   : 0
% 1.20/1.42  # Backward-subsumed                    : 2
% 1.20/1.42  # Backward-rewritten                   : 200
% 1.20/1.42  # Generated clauses                    : 121616
% 1.20/1.42  # ...of the previous two non-trivial   : 118017
% 1.20/1.42  # Contextual simplify-reflections      : 8
% 1.20/1.42  # Paramodulations                      : 121570
% 1.20/1.42  # Factorizations                       : 0
% 1.20/1.42  # Equation resolutions                 : 47
% 1.20/1.42  # Propositional unsat checks           : 0
% 1.20/1.42  #    Propositional check models        : 0
% 1.20/1.42  #    Propositional check unsatisfiable : 0
% 1.20/1.42  #    Propositional clauses             : 0
% 1.20/1.42  #    Propositional clauses after purity: 0
% 1.20/1.42  #    Propositional unsat core size     : 0
% 1.20/1.42  #    Propositional preprocessing time  : 0.000
% 1.20/1.42  #    Propositional encoding time       : 0.000
% 1.20/1.42  #    Propositional solver time         : 0.000
% 1.20/1.42  #    Success case prop preproc time    : 0.000
% 1.20/1.42  #    Success case prop encoding time   : 0.000
% 1.20/1.42  #    Success case prop solver time     : 0.000
% 1.20/1.42  # Current number of processed clauses  : 920
% 1.20/1.42  #    Positive orientable unit clauses  : 16
% 1.20/1.42  #    Positive unorientable unit clauses: 0
% 1.20/1.42  #    Negative unit clauses             : 8
% 1.20/1.42  #    Non-unit-clauses                  : 896
% 1.20/1.42  # Current number of unprocessed clauses: 108884
% 1.20/1.42  # ...number of literals in the above   : 497261
% 1.20/1.42  # Current number of archived formulas  : 0
% 1.20/1.42  # Current number of archived clauses   : 202
% 1.20/1.42  # Clause-clause subsumption calls (NU) : 121492
% 1.20/1.42  # Rec. Clause-clause subsumption calls : 57039
% 1.20/1.42  # Non-unit clause-clause subsumptions  : 4083
% 1.20/1.42  # Unit Clause-clause subsumption calls : 600
% 1.20/1.42  # Rewrite failures with RHS unbound    : 0
% 1.20/1.42  # BW rewrite match attempts            : 18
% 1.20/1.42  # BW rewrite match successes           : 10
% 1.20/1.42  # Condensation attempts                : 0
% 1.20/1.42  # Condensation successes               : 0
% 1.20/1.42  # Termbank termtop insertions          : 1992849
% 1.20/1.43  
% 1.20/1.43  # -------------------------------------------------
% 1.20/1.43  # User time                : 1.027 s
% 1.20/1.43  # System time              : 0.058 s
% 1.20/1.43  # Total time               : 1.085 s
% 1.20/1.43  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
