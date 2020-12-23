%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 149 expanded)
%              Number of clauses        :   45 (  62 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 ( 610 expanded)
%              Number of equality atoms :   68 ( 104 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,negated_conjecture,(
    ! [X59] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ m1_subset_1(X59,esk5_0)
        | ~ r2_hidden(X59,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X59) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X26] : ~ v1_xboole_0(k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | ~ r1_tarski(esk3_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r1_tarski(esk3_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_27,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_relset_1(X44,X45,X46) = k1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_33,plain,(
    ! [X51,X52,X53] :
      ( ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X53 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X53 != k1_xboole_0
        | v1_funct_2(X53,X51,X52)
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ( k2_zfmisc_1(X24,X25) != k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k2_zfmisc_1(X24,X25) = k1_xboole_0 )
      & ( X25 != k1_xboole_0
        | k2_zfmisc_1(X24,X25) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X36,X37,X38,X40] :
      ( ( r2_hidden(esk4_3(X36,X37,X38),k1_relat_1(X38))
        | ~ r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(k4_tarski(esk4_3(X36,X37,X38),X36),X38)
        | ~ r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(esk4_3(X36,X37,X38),X37)
        | ~ r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) )
      & ( ~ r2_hidden(X40,k1_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X40,X36),X38)
        | ~ r2_hidden(X40,X37)
        | r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_40,plain,(
    ! [X31] :
      ( ~ v1_xboole_0(X31)
      | v1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_41,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k7_relset_1(X47,X48,X49,X50) = k9_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_45,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k1_relat_1(esk8_0)
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_23])])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k1_relat_1(esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_58,plain,(
    ! [X41,X42,X43] :
      ( ( r2_hidden(X41,k1_relat_1(X43))
        | ~ r2_hidden(k4_tarski(X41,X42),X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( X42 = k1_funct_1(X43,X41)
        | ~ r2_hidden(k4_tarski(X41,X42),X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( ~ r2_hidden(X41,k1_relat_1(X43))
        | X42 != k1_funct_1(X43,X41)
        | r2_hidden(k4_tarski(X41,X42),X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_59,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | v1_relat_1(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_60,plain,(
    ! [X34,X35] : v1_relat_1(k2_zfmisc_1(X34,X35)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k1_relat_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_63,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( esk9_0 != k1_funct_1(esk8_0,X1)
    | ~ m1_subset_1(X1,k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( k1_funct_1(X1,esk4_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_23]),c_0_65])])).

fof(c_0_70,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | m1_subset_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_71,negated_conjecture,
    ( esk9_0 != X1
    | ~ m1_subset_1(esk4_3(X1,X2,esk8_0),k1_relat_1(esk8_0))
    | ~ r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk9_0 != X1
    | ~ r2_hidden(esk4_3(X1,X2,esk8_0),k1_relat_1(esk8_0))
    | ~ r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_75,negated_conjecture,
    ( esk9_0 != X1
    | ~ r2_hidden(esk4_3(X1,esk7_0,esk8_0),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_69])])).

cnf(c_0_76,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( esk9_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_69])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_77,c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.029 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 0.13/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.41  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.41  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.13/0.41  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.13/0.41  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.13/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.41  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.41  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 0.13/0.41  fof(c_0_18, plain, ![X29, X30]:(~m1_subset_1(X29,X30)|(v1_xboole_0(X30)|r2_hidden(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.41  fof(c_0_19, negated_conjecture, ![X59]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~m1_subset_1(X59,esk5_0)|(~r2_hidden(X59,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X59))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.13/0.41  fof(c_0_20, plain, ![X26]:~v1_xboole_0(k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.41  fof(c_0_21, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk3_2(X21,X22),X22)|~r1_tarski(esk3_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk3_2(X21,X22),X22)|r1_tarski(esk3_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.41  cnf(c_0_22, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_24, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.13/0.41  fof(c_0_27, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (r1_tarski(esk8_0,X1)|k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.41  fof(c_0_29, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.41  cnf(c_0_31, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(er,[status(thm)],[c_0_28])).
% 0.13/0.41  fof(c_0_32, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k1_relset_1(X44,X45,X46)=k1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.41  fof(c_0_33, plain, ![X51, X52, X53]:((((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((~v1_funct_2(X53,X51,X52)|X53=k1_xboole_0|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X53!=k1_xboole_0|v1_funct_2(X53,X51,X52)|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.41  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.41  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.41  fof(c_0_36, plain, ![X24, X25]:((k2_zfmisc_1(X24,X25)!=k1_xboole_0|(X24=k1_xboole_0|X25=k1_xboole_0))&((X24!=k1_xboole_0|k2_zfmisc_1(X24,X25)=k1_xboole_0)&(X25!=k1_xboole_0|k2_zfmisc_1(X24,X25)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.41  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_38, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.41  fof(c_0_39, plain, ![X36, X37, X38, X40]:((((r2_hidden(esk4_3(X36,X37,X38),k1_relat_1(X38))|~r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38))&(r2_hidden(k4_tarski(esk4_3(X36,X37,X38),X36),X38)|~r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38)))&(r2_hidden(esk4_3(X36,X37,X38),X37)|~r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38)))&(~r2_hidden(X40,k1_relat_1(X38))|~r2_hidden(k4_tarski(X40,X36),X38)|~r2_hidden(X40,X37)|r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.13/0.41  fof(c_0_40, plain, ![X31]:(~v1_xboole_0(X31)|v1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.13/0.41  fof(c_0_41, plain, ![X47, X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k7_relset_1(X47,X48,X49,X50)=k9_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.13/0.41  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk8_0)|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.41  cnf(c_0_43, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.41  cnf(c_0_44, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.41  cnf(c_0_45, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_47, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.41  cnf(c_0_48, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_50, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.41  cnf(c_0_51, negated_conjecture, (esk6_0!=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (esk5_0=k1_relat_1(esk8_0)|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23])])).
% 0.13/0.41  cnf(c_0_53, plain, (~r2_hidden(X1,k9_relat_1(X2,X3))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_48])).
% 0.13/0.41  cnf(c_0_54, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_23])])).
% 0.13/0.41  cnf(c_0_55, negated_conjecture, (esk5_0=k1_relat_1(esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.41  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.41  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.41  fof(c_0_58, plain, ![X41, X42, X43]:(((r2_hidden(X41,k1_relat_1(X43))|~r2_hidden(k4_tarski(X41,X42),X43)|(~v1_relat_1(X43)|~v1_funct_1(X43)))&(X42=k1_funct_1(X43,X41)|~r2_hidden(k4_tarski(X41,X42),X43)|(~v1_relat_1(X43)|~v1_funct_1(X43))))&(~r2_hidden(X41,k1_relat_1(X43))|X42!=k1_funct_1(X43,X41)|r2_hidden(k4_tarski(X41,X42),X43)|(~v1_relat_1(X43)|~v1_funct_1(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.41  fof(c_0_59, plain, ![X32, X33]:(~v1_relat_1(X32)|(~m1_subset_1(X33,k1_zfmisc_1(X32))|v1_relat_1(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.41  fof(c_0_60, plain, ![X34, X35]:v1_relat_1(k2_zfmisc_1(X34,X35)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, (esk5_0=k1_relat_1(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.13/0.41  cnf(c_0_63, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.41  cnf(c_0_64, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.41  cnf(c_0_65, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.41  cnf(c_0_66, negated_conjecture, (esk9_0!=k1_funct_1(esk8_0,X1)|~m1_subset_1(X1,k1_relat_1(esk8_0))|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.41  cnf(c_0_67, plain, (k1_funct_1(X1,esk4_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_63, c_0_47])).
% 0.13/0.41  cnf(c_0_68, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_23]), c_0_65])])).
% 0.13/0.41  fof(c_0_70, plain, ![X27, X28]:(~r2_hidden(X27,X28)|m1_subset_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.41  cnf(c_0_71, negated_conjecture, (esk9_0!=X1|~m1_subset_1(esk4_3(X1,X2,esk8_0),k1_relat_1(esk8_0))|~r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])])).
% 0.13/0.41  cnf(c_0_72, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.41  cnf(c_0_73, negated_conjecture, (esk9_0!=X1|~r2_hidden(esk4_3(X1,X2,esk8_0),k1_relat_1(esk8_0))|~r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.41  cnf(c_0_74, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.41  cnf(c_0_75, negated_conjecture, (esk9_0!=X1|~r2_hidden(esk4_3(X1,esk7_0,esk8_0),k1_relat_1(esk8_0))|~r2_hidden(X1,k9_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_69])])).
% 0.13/0.41  cnf(c_0_76, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.41  cnf(c_0_77, negated_conjecture, (esk9_0!=X1|~r2_hidden(X1,k9_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_69])])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_77, c_0_54]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 79
% 0.13/0.41  # Proof object clause steps            : 45
% 0.13/0.41  # Proof object formula steps           : 34
% 0.13/0.41  # Proof object conjectures             : 26
% 0.13/0.41  # Proof object clause conjectures      : 23
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 24
% 0.13/0.41  # Proof object initial formulas used   : 17
% 0.13/0.41  # Proof object generating inferences   : 20
% 0.13/0.41  # Proof object simplifying inferences  : 19
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 17
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 39
% 0.13/0.41  # Removed in clause preprocessing      : 0
% 0.13/0.41  # Initial clauses in saturation        : 39
% 0.13/0.41  # Processed clauses                    : 487
% 0.13/0.41  # ...of these trivial                  : 5
% 0.13/0.41  # ...subsumed                          : 151
% 0.13/0.41  # ...remaining for further processing  : 331
% 0.13/0.41  # Other redundant clauses eliminated   : 4
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 7
% 0.13/0.41  # Backward-rewritten                   : 37
% 0.13/0.41  # Generated clauses                    : 737
% 0.13/0.41  # ...of the previous two non-trivial   : 709
% 0.13/0.41  # Contextual simplify-reflections      : 9
% 0.13/0.41  # Paramodulations                      : 676
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 61
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 248
% 0.13/0.41  #    Positive orientable unit clauses  : 29
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 6
% 0.13/0.41  #    Non-unit-clauses                  : 213
% 0.13/0.41  # Current number of unprocessed clauses: 248
% 0.13/0.41  # ...number of literals in the above   : 1068
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 83
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 5512
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 2637
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 147
% 0.13/0.41  # Unit Clause-clause subsumption calls : 80
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 73
% 0.13/0.41  # BW rewrite match successes           : 3
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 14274
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.060 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.067 s
% 0.19/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
