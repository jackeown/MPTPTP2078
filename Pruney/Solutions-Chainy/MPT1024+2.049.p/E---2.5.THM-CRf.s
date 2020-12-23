%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:33 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 (4055 expanded)
%              Number of clauses        :   63 (1558 expanded)
%              Number of leaves         :   12 (1016 expanded)
%              Depth                    :   22
%              Number of atoms          :  273 (18537 expanded)
%              Number of equality atoms :   76 (3292 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X34,k1_relat_1(X36))
        | ~ r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( X35 = k1_funct_1(X36,X34)
        | ~ r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(X34,k1_relat_1(X36))
        | X35 != k1_funct_1(X36,X34)
        | r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_14,plain,(
    ! [X17,X18,X19,X21] :
      ( ( r2_hidden(esk1_3(X17,X18,X19),k1_relat_1(X19))
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk1_3(X17,X18,X19),X17),X19)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(X21,k1_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X21,X17),X19)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,negated_conjecture,(
    ! [X59] :
      ( v1_funct_1(esk10_0)
      & v1_funct_2(esk10_0,esk7_0,esk8_0)
      & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
      & r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0))
      & ( ~ r2_hidden(X59,esk7_0)
        | ~ r2_hidden(X59,esk9_0)
        | esk11_0 != k1_funct_1(esk10_0,X59) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_18,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k1_relset_1(X37,X38,X39) = k1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k7_relset_1(X40,X41,X42,X43) = k9_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_25,plain,(
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

cnf(c_0_26,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0)
    | esk11_0 != k1_funct_1(esk10_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(esk7_0,esk8_0,esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk11_0,X1,esk10_0),esk7_0)
    | ~ r2_hidden(esk1_3(esk11_0,X1,esk10_0),esk9_0)
    | ~ r2_hidden(esk11_0,k9_relat_1(esk10_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk11_0,k9_relat_1(esk10_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_22])])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_34]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk11_0,esk9_0,esk10_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_30])])).

cnf(c_0_42,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk10_0),esk7_0)
    | ~ r2_hidden(X1,k9_relat_1(esk10_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_30])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_44])).

cnf(c_0_48,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

fof(c_0_50,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_51,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,negated_conjecture,
    ( k1_relset_1(esk7_0,k1_xboole_0,esk10_0) = k1_relat_1(esk10_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_53,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | v1_funct_2(esk10_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_49])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk10_0) = k1_relat_1(esk10_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk10_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

fof(c_0_60,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ r2_hidden(X10,X9)
      | r2_hidden(X10,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk10_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_65,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk11_0,esk9_0,esk10_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_67,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk10_0),k1_xboole_0)
    | ~ r2_hidden(X1,k9_relat_1(esk10_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_62]),c_0_30])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_69,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_23])).

cnf(c_0_71,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_38])])).

fof(c_0_72,plain,(
    ! [X44,X45,X46,X48,X49] :
      ( ( r2_hidden(esk5_3(X44,X45,X46),X45)
        | k1_relset_1(X45,X44,X46) = X45
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X44,X45,X46),X48),X46)
        | k1_relset_1(X45,X44,X46) = X45
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))) )
      & ( k1_relset_1(X45,X44,X46) != X45
        | ~ r2_hidden(X49,X45)
        | r2_hidden(k4_tarski(X49,esk6_4(X44,X45,X46,X49)),X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_73,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(k1_xboole_0,X1)),X2)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_71])).

cnf(c_0_75,plain,
    ( k1_relset_1(X2,X1,X3) = X2
    | ~ r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X4),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(k1_xboole_0,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_77,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | k1_relset_1(X2,X1,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ r2_hidden(esk5_3(X2,X1,X3),k1_relat_1(k1_xboole_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | r2_hidden(esk5_3(X1,k1_xboole_0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_77])).

cnf(c_0_80,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_81,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_61])).

cnf(c_0_82,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_61]),c_0_81])).

cnf(c_0_83,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_82]),c_0_70])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk11_0,esk9_0,k1_xboole_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_71])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),X3)
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk11_0,k9_relat_1(k1_xboole_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_71])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.028 s
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.21/0.40  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.40  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.21/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.40  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 0.21/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.21/0.40  fof(c_0_13, plain, ![X34, X35, X36]:(((r2_hidden(X34,k1_relat_1(X36))|~r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(X35=k1_funct_1(X36,X34)|~r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(~r2_hidden(X34,k1_relat_1(X36))|X35!=k1_funct_1(X36,X34)|r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.40  fof(c_0_14, plain, ![X17, X18, X19, X21]:((((r2_hidden(esk1_3(X17,X18,X19),k1_relat_1(X19))|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk1_3(X17,X18,X19),X17),X19)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(r2_hidden(esk1_3(X17,X18,X19),X18)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(~r2_hidden(X21,k1_relat_1(X19))|~r2_hidden(k4_tarski(X21,X17),X19)|~r2_hidden(X21,X18)|r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.21/0.40  fof(c_0_15, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.40  fof(c_0_16, negated_conjecture, ![X59]:(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,esk8_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&(r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0))&(~r2_hidden(X59,esk7_0)|~r2_hidden(X59,esk9_0)|esk11_0!=k1_funct_1(esk10_0,X59)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.21/0.40  fof(c_0_17, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.40  fof(c_0_18, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k1_relset_1(X37,X38,X39)=k1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.40  cnf(c_0_19, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  fof(c_0_24, plain, ![X40, X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k7_relset_1(X40,X41,X42,X43)=k9_relat_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.40  fof(c_0_25, plain, ![X51, X52, X53]:((((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((~v1_funct_2(X53,X51,X52)|X53=k1_xboole_0|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X53!=k1_xboole_0|v1_funct_2(X53,X51,X52)|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.40  cnf(c_0_26, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk9_0)|esk11_0!=k1_funct_1(esk10_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_28, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.40  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(esk11_0,k7_relset_1(esk7_0,esk8_0,esk10_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_32, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.40  cnf(c_0_33, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (k1_relset_1(esk7_0,esk8_0,esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_26, c_0_22])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk1_3(esk11_0,X1,esk10_0),esk7_0)|~r2_hidden(esk1_3(esk11_0,X1,esk10_0),esk9_0)|~r2_hidden(esk11_0,k9_relat_1(esk10_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])])).
% 0.21/0.40  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk11_0,k9_relat_1(esk10_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_22])])).
% 0.21/0.40  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, (k1_relat_1(esk10_0)=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_34]), c_0_35])])).
% 0.21/0.40  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk1_3(esk11_0,esk9_0,esk10_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_30])])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk10_0),esk7_0)|~r2_hidden(X1,k9_relat_1(esk10_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_30])])).
% 0.21/0.40  cnf(c_0_43, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_38])])).
% 0.21/0.40  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_43])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_22, c_0_44])).
% 0.21/0.40  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_35, c_0_44])).
% 0.21/0.40  cnf(c_0_48, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_49, negated_conjecture, (esk10_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.21/0.40  fof(c_0_50, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.40  fof(c_0_51, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.40  cnf(c_0_52, negated_conjecture, (k1_relset_1(esk7_0,k1_xboole_0,esk10_0)=k1_relat_1(esk10_0)), inference(rw,[status(thm)],[c_0_34, c_0_44])).
% 0.21/0.40  cnf(c_0_53, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_48])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (esk10_0=k1_xboole_0|m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_46, c_0_49])).
% 0.21/0.40  cnf(c_0_55, negated_conjecture, (esk10_0=k1_xboole_0|v1_funct_2(esk10_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_49])).
% 0.21/0.40  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.40  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.40  cnf(c_0_58, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk10_0)=k1_relat_1(esk10_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 0.21/0.40  cnf(c_0_59, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk10_0)=k1_xboole_0|esk10_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.21/0.40  fof(c_0_60, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|(~r2_hidden(X10,X9)|r2_hidden(X10,X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.40  cnf(c_0_61, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.40  cnf(c_0_62, negated_conjecture, (k1_relat_1(esk10_0)=k1_xboole_0|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.40  cnf(c_0_63, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.40  cnf(c_0_64, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_65, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_61])).
% 0.21/0.40  cnf(c_0_66, negated_conjecture, (esk10_0=k1_xboole_0|~r2_hidden(esk1_3(esk11_0,esk9_0,esk10_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 0.21/0.40  cnf(c_0_67, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk10_0),k1_xboole_0)|~r2_hidden(X1,k9_relat_1(esk10_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_62]), c_0_30])])).
% 0.21/0.40  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_61])).
% 0.21/0.40  cnf(c_0_69, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_64])).
% 0.21/0.40  cnf(c_0_70, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_23])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, (esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_38])])).
% 0.21/0.40  fof(c_0_72, plain, ![X44, X45, X46, X48, X49]:(((r2_hidden(esk5_3(X44,X45,X46),X45)|k1_relset_1(X45,X44,X46)=X45|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))&(~r2_hidden(k4_tarski(esk5_3(X44,X45,X46),X48),X46)|k1_relset_1(X45,X44,X46)=X45|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))))&(k1_relset_1(X45,X44,X46)!=X45|(~r2_hidden(X49,X45)|r2_hidden(k4_tarski(X49,esk6_4(X44,X45,X46,X49)),X46))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.21/0.40  cnf(c_0_73, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(k1_xboole_0,X1)),X2)|~v1_funct_1(k1_xboole_0)|~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.21/0.40  cnf(c_0_74, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_29, c_0_71])).
% 0.21/0.40  cnf(c_0_75, plain, (k1_relset_1(X2,X1,X3)=X2|~r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X4),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.40  cnf(c_0_76, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(k1_xboole_0,X1)),X2)|~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.21/0.40  cnf(c_0_77, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|k1_relset_1(X2,X1,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.40  cnf(c_0_78, plain, (k1_relset_1(X1,X2,X3)=X1|~r2_hidden(esk5_3(X2,X1,X3),k1_relat_1(k1_xboole_0))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.40  cnf(c_0_79, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|r2_hidden(esk5_3(X1,k1_xboole_0,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_68, c_0_77])).
% 0.21/0.40  cnf(c_0_80, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.40  cnf(c_0_81, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_61])).
% 0.21/0.40  cnf(c_0_82, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_61]), c_0_81])).
% 0.21/0.40  cnf(c_0_83, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_82]), c_0_70])])).
% 0.21/0.40  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk1_3(esk11_0,esk9_0,k1_xboole_0),esk7_0)), inference(rw,[status(thm)],[c_0_41, c_0_71])).
% 0.21/0.40  cnf(c_0_85, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),X3)|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_68, c_0_83])).
% 0.21/0.40  cnf(c_0_86, negated_conjecture, (r2_hidden(esk11_0,k9_relat_1(k1_xboole_0,esk9_0))), inference(rw,[status(thm)],[c_0_38, c_0_71])).
% 0.21/0.40  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 88
% 0.21/0.40  # Proof object clause steps            : 63
% 0.21/0.40  # Proof object formula steps           : 25
% 0.21/0.40  # Proof object conjectures             : 32
% 0.21/0.40  # Proof object clause conjectures      : 29
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 22
% 0.21/0.40  # Proof object initial formulas used   : 12
% 0.21/0.40  # Proof object generating inferences   : 31
% 0.21/0.40  # Proof object simplifying inferences  : 43
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 13
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 37
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 37
% 0.21/0.40  # Processed clauses                    : 278
% 0.21/0.40  # ...of these trivial                  : 2
% 0.21/0.40  # ...subsumed                          : 108
% 0.21/0.40  # ...remaining for further processing  : 168
% 0.21/0.40  # Other redundant clauses eliminated   : 38
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 8
% 0.21/0.40  # Backward-rewritten                   : 80
% 0.21/0.40  # Generated clauses                    : 523
% 0.21/0.40  # ...of the previous two non-trivial   : 542
% 0.21/0.40  # Contextual simplify-reflections      : 8
% 0.21/0.40  # Paramodulations                      : 487
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 38
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 71
% 0.21/0.40  #    Positive orientable unit clauses  : 13
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 3
% 0.21/0.40  #    Non-unit-clauses                  : 55
% 0.21/0.40  # Current number of unprocessed clauses: 260
% 0.21/0.40  # ...number of literals in the above   : 1401
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 88
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 2179
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 661
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 119
% 0.21/0.40  # Unit Clause-clause subsumption calls : 70
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 11
% 0.21/0.40  # BW rewrite match successes           : 5
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 14312
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.050 s
% 0.21/0.40  # System time              : 0.006 s
% 0.21/0.40  # Total time               : 0.056 s
% 0.21/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
