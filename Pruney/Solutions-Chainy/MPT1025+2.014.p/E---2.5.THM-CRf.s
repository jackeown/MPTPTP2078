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
% DateTime   : Thu Dec  3 11:06:37 EST 2020

% Result     : Theorem 23.39s
% Output     : CNFRefutation 23.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 390 expanded)
%              Number of clauses        :   51 ( 163 expanded)
%              Number of leaves         :   13 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  300 (1689 expanded)
%              Number of equality atoms :   17 ( 153 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t52_relset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X61] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ m1_subset_1(X61,esk5_0)
        | ~ r2_hidden(X61,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X61) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ( ~ v4_relat_1(X23,X22)
        | r1_tarski(k1_relat_1(X23),X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_tarski(k1_relat_1(X23),X22)
        | v4_relat_1(X23,X22)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_18,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k7_relset_1(X45,X46,X47,X48) = k9_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_22,plain,(
    ! [X24,X25,X26,X28] :
      ( ( r2_hidden(esk3_3(X24,X25,X26),k1_relat_1(X26))
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk3_3(X24,X25,X26),X24),X26)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X25)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X28,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X28,X24),X26)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_23,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_relat_1(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_27,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_37,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | m1_subset_1(k7_relset_1(X41,X42,X43,X44),k1_zfmisc_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(X1,X4,X2),X3)
    | ~ r2_hidden(X1,k9_relat_1(X2,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(X1,X2,esk8_0,esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19])])).

fof(c_0_43,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v5_relat_1(X30,X29)
      | ~ v1_funct_1(X30)
      | ~ r2_hidden(X31,k1_relat_1(X30))
      | r2_hidden(k1_funct_1(X30,X31),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_44,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_45,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X32,k1_relat_1(X34))
        | ~ r2_hidden(k4_tarski(X32,X33),X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( X33 = k1_funct_1(X34,X32)
        | ~ r2_hidden(k4_tarski(X32,X33),X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( ~ r2_hidden(X32,k1_relat_1(X34))
        | X33 != k1_funct_1(X34,X32)
        | r2_hidden(k4_tarski(X32,X33),X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_46,plain,(
    ! [X49,X50,X51,X52,X53,X55] :
      ( ( m1_subset_1(esk4_5(X49,X50,X51,X52,X53),X51)
        | ~ r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( r2_hidden(k4_tarski(esk4_5(X49,X50,X51,X52,X53),X53),X52)
        | ~ r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( r2_hidden(esk4_5(X49,X50,X51,X52,X53),X50)
        | ~ r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( ~ m1_subset_1(X55,X51)
        | ~ r2_hidden(k4_tarski(X55,X53),X52)
        | ~ r2_hidden(X55,X50)
        | r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,esk5_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(X1,X3,X2),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_52,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v5_relat_1(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk8_0,esk5_0))
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_26])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_26])])).

cnf(c_0_62,plain,
    ( k1_funct_1(X1,esk3_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_30])).

cnf(c_0_63,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,plain,
    ( k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_20]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(esk3_3(X1,X2,esk8_0),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_54]),c_0_26])])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk9_0 != X3
    | ~ m1_subset_1(esk4_5(X2,X4,X1,esk8_0,X3),esk5_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk4_5(X2,X4,X1,esk8_0,X3),esk7_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk8_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_54])])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_65]),c_0_26])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_31]),c_0_26])])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk9_0 != X2
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r2_hidden(esk4_5(X1,X3,esk5_0,esk8_0,X2),esk7_0)
    | ~ r2_hidden(X2,k7_relset_1(esk5_0,X1,esk8_0,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_57]),c_0_58])).

cnf(c_0_72,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_60]),c_0_26])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk9_0 != X2
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk5_0,X1,esk8_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_69]),c_0_73]),c_0_57])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_34]),c_0_19])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:21:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 23.39/23.67  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 23.39/23.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 23.39/23.67  #
% 23.39/23.67  # Preprocessing time       : 0.029 s
% 23.39/23.67  # Presaturation interreduction done
% 23.39/23.67  
% 23.39/23.67  # Proof found!
% 23.39/23.67  # SZS status Theorem
% 23.39/23.67  # SZS output start CNFRefutation
% 23.39/23.67  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 23.39/23.67  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.39/23.67  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.39/23.67  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 23.39/23.67  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 23.39/23.67  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 23.39/23.67  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 23.39/23.67  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 23.39/23.67  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 23.39/23.67  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 23.39/23.67  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 23.39/23.67  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 23.39/23.67  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 23.39/23.67  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 23.39/23.67  fof(c_0_14, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 23.39/23.67  fof(c_0_15, negated_conjecture, ![X61]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~m1_subset_1(X61,esk5_0)|(~r2_hidden(X61,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X61))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 23.39/23.67  fof(c_0_16, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 23.39/23.67  fof(c_0_17, plain, ![X22, X23]:((~v4_relat_1(X23,X22)|r1_tarski(k1_relat_1(X23),X22)|~v1_relat_1(X23))&(~r1_tarski(k1_relat_1(X23),X22)|v4_relat_1(X23,X22)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 23.39/23.67  cnf(c_0_18, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 23.39/23.67  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.39/23.67  cnf(c_0_20, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 23.39/23.67  fof(c_0_21, plain, ![X45, X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k7_relset_1(X45,X46,X47,X48)=k9_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 23.39/23.67  fof(c_0_22, plain, ![X24, X25, X26, X28]:((((r2_hidden(esk3_3(X24,X25,X26),k1_relat_1(X26))|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk3_3(X24,X25,X26),X24),X26)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(r2_hidden(esk3_3(X24,X25,X26),X25)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(~r2_hidden(X28,k1_relat_1(X26))|~r2_hidden(k4_tarski(X28,X24),X26)|~r2_hidden(X28,X25)|r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 23.39/23.67  fof(c_0_23, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 23.39/23.67  cnf(c_0_24, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 23.39/23.67  cnf(c_0_25, negated_conjecture, (v4_relat_1(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 23.39/23.67  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 23.39/23.67  cnf(c_0_27, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 23.39/23.67  fof(c_0_28, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 23.39/23.67  cnf(c_0_29, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 23.39/23.67  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 23.39/23.67  cnf(c_0_31, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 23.39/23.67  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 23.39/23.67  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 23.39/23.67  cnf(c_0_34, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.39/23.67  cnf(c_0_35, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 23.39/23.67  fof(c_0_36, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 23.39/23.67  fof(c_0_37, plain, ![X41, X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|m1_subset_1(k7_relset_1(X41,X42,X43,X44),k1_zfmisc_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 23.39/23.67  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 23.39/23.67  cnf(c_0_39, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 23.39/23.67  cnf(c_0_40, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(esk3_3(X1,X4,X2),X3)|~r2_hidden(X1,k9_relat_1(X2,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 23.39/23.67  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 23.39/23.67  cnf(c_0_42, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(X1,X2,esk8_0,esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19])])).
% 23.39/23.67  fof(c_0_43, plain, ![X29, X30, X31]:(~v1_relat_1(X30)|~v5_relat_1(X30,X29)|~v1_funct_1(X30)|(~r2_hidden(X31,k1_relat_1(X30))|r2_hidden(k1_funct_1(X30,X31),X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 23.39/23.67  cnf(c_0_44, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 23.39/23.67  fof(c_0_45, plain, ![X32, X33, X34]:(((r2_hidden(X32,k1_relat_1(X34))|~r2_hidden(k4_tarski(X32,X33),X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(X33=k1_funct_1(X34,X32)|~r2_hidden(k4_tarski(X32,X33),X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(~r2_hidden(X32,k1_relat_1(X34))|X33!=k1_funct_1(X34,X32)|r2_hidden(k4_tarski(X32,X33),X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 23.39/23.67  fof(c_0_46, plain, ![X49, X50, X51, X52, X53, X55]:((((m1_subset_1(esk4_5(X49,X50,X51,X52,X53),X51)|~r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49))&(r2_hidden(k4_tarski(esk4_5(X49,X50,X51,X52,X53),X53),X52)|~r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49)))&(r2_hidden(esk4_5(X49,X50,X51,X52,X53),X50)|~r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49)))&(~m1_subset_1(X55,X51)|~r2_hidden(k4_tarski(X55,X53),X52)|~r2_hidden(X55,X50)|r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 23.39/23.67  cnf(c_0_47, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 23.39/23.67  cnf(c_0_48, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 23.39/23.67  cnf(c_0_49, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 23.39/23.67  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,esk5_0))|~v1_relat_1(X2)|~r2_hidden(esk3_3(X1,X3,X2),k1_relat_1(esk8_0))|~r2_hidden(X1,k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 23.39/23.67  cnf(c_0_51, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 23.39/23.67  cnf(c_0_52, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 23.39/23.67  cnf(c_0_53, negated_conjecture, (v5_relat_1(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_19])).
% 23.39/23.67  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.39/23.67  cnf(c_0_55, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 23.39/23.67  cnf(c_0_56, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 23.39/23.67  cnf(c_0_57, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 23.39/23.67  cnf(c_0_58, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_20])).
% 23.39/23.67  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk8_0,esk5_0))|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_26])])).
% 23.39/23.67  cnf(c_0_60, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_19])).
% 23.39/23.67  cnf(c_0_61, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),esk6_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_26])])).
% 23.39/23.67  cnf(c_0_62, plain, (k1_funct_1(X1,esk3_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_55, c_0_30])).
% 23.39/23.67  cnf(c_0_63, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.39/23.67  cnf(c_0_64, plain, (k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_20]), c_0_58])).
% 23.39/23.67  cnf(c_0_65, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk5_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 23.39/23.67  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(esk3_3(X1,X2,esk8_0),k1_relat_1(esk8_0))|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_54]), c_0_26])])).
% 23.39/23.67  cnf(c_0_67, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk9_0!=X3|~m1_subset_1(esk4_5(X2,X4,X1,esk8_0,X3),esk5_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk4_5(X2,X4,X1,esk8_0,X3),esk7_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk8_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_54])])).
% 23.39/23.68  cnf(c_0_68, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 23.39/23.68  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_65]), c_0_26])])).
% 23.39/23.68  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_31]), c_0_26])])).
% 23.39/23.68  cnf(c_0_71, negated_conjecture, (v1_xboole_0(X1)|esk9_0!=X2|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r2_hidden(esk4_5(X1,X3,esk5_0,esk8_0,X2),esk7_0)|~r2_hidden(X2,k7_relset_1(esk5_0,X1,esk8_0,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_57]), c_0_58])).
% 23.39/23.68  cnf(c_0_72, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 23.39/23.68  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_60]), c_0_26])])).
% 23.39/23.68  cnf(c_0_74, negated_conjecture, (r2_hidden(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_60])).
% 23.39/23.68  cnf(c_0_75, negated_conjecture, (v1_xboole_0(X1)|esk9_0!=X2|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r2_hidden(X2,k7_relset_1(esk5_0,X1,esk8_0,esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_69]), c_0_73]), c_0_57])).
% 23.39/23.68  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_74])).
% 23.39/23.68  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_34]), c_0_19])]), c_0_76]), ['proof']).
% 23.39/23.68  # SZS output end CNFRefutation
% 23.39/23.68  # Proof object total steps             : 78
% 23.39/23.68  # Proof object clause steps            : 51
% 23.39/23.68  # Proof object formula steps           : 27
% 23.39/23.68  # Proof object conjectures             : 29
% 23.39/23.68  # Proof object clause conjectures      : 26
% 23.39/23.68  # Proof object formula conjectures     : 3
% 23.39/23.68  # Proof object initial clauses used    : 22
% 23.39/23.68  # Proof object initial formulas used   : 13
% 23.39/23.68  # Proof object generating inferences   : 29
% 23.39/23.68  # Proof object simplifying inferences  : 34
% 23.39/23.68  # Training examples: 0 positive, 0 negative
% 23.39/23.68  # Parsed axioms                        : 14
% 23.39/23.68  # Removed by relevancy pruning/SinE    : 0
% 23.39/23.68  # Initial clauses                      : 33
% 23.39/23.68  # Removed in clause preprocessing      : 0
% 23.39/23.68  # Initial clauses in saturation        : 33
% 23.39/23.68  # Processed clauses                    : 100338
% 23.39/23.68  # ...of these trivial                  : 2
% 23.39/23.68  # ...subsumed                          : 96225
% 23.39/23.68  # ...remaining for further processing  : 4111
% 23.39/23.68  # Other redundant clauses eliminated   : 12
% 23.39/23.68  # Clauses deleted for lack of memory   : 0
% 23.39/23.68  # Backward-subsumed                    : 433
% 23.39/23.68  # Backward-rewritten                   : 11
% 23.39/23.68  # Generated clauses                    : 1644810
% 23.39/23.68  # ...of the previous two non-trivial   : 1643858
% 23.39/23.68  # Contextual simplify-reflections      : 756
% 23.39/23.68  # Paramodulations                      : 1644797
% 23.39/23.68  # Factorizations                       : 0
% 23.39/23.68  # Equation resolutions                 : 13
% 23.39/23.68  # Propositional unsat checks           : 0
% 23.39/23.68  #    Propositional check models        : 0
% 23.39/23.68  #    Propositional check unsatisfiable : 0
% 23.39/23.68  #    Propositional clauses             : 0
% 23.39/23.68  #    Propositional clauses after purity: 0
% 23.39/23.68  #    Propositional unsat core size     : 0
% 23.39/23.68  #    Propositional preprocessing time  : 0.000
% 23.39/23.68  #    Propositional encoding time       : 0.000
% 23.39/23.68  #    Propositional solver time         : 0.000
% 23.39/23.68  #    Success case prop preproc time    : 0.000
% 23.39/23.68  #    Success case prop encoding time   : 0.000
% 23.39/23.68  #    Success case prop solver time     : 0.000
% 23.39/23.68  # Current number of processed clauses  : 3633
% 23.39/23.68  #    Positive orientable unit clauses  : 21
% 23.39/23.68  #    Positive unorientable unit clauses: 0
% 23.39/23.68  #    Negative unit clauses             : 8
% 23.39/23.68  #    Non-unit-clauses                  : 3604
% 23.39/23.68  # Current number of unprocessed clauses: 1537018
% 23.39/23.68  # ...number of literals in the above   : 14568320
% 23.39/23.68  # Current number of archived formulas  : 0
% 23.39/23.68  # Current number of archived clauses   : 476
% 23.39/23.68  # Clause-clause subsumption calls (NU) : 6717342
% 23.39/23.68  # Rec. Clause-clause subsumption calls : 453948
% 23.39/23.68  # Non-unit clause-clause subsumptions  : 58450
% 23.39/23.68  # Unit Clause-clause subsumption calls : 593
% 23.39/23.68  # Rewrite failures with RHS unbound    : 0
% 23.39/23.68  # BW rewrite match attempts            : 9
% 23.39/23.68  # BW rewrite match successes           : 2
% 23.39/23.68  # Condensation attempts                : 0
% 23.39/23.68  # Condensation successes               : 0
% 23.39/23.68  # Termbank termtop insertions          : 47182265
% 23.46/23.74  
% 23.46/23.74  # -------------------------------------------------
% 23.46/23.74  # User time                : 22.610 s
% 23.46/23.74  # System time              : 0.752 s
% 23.46/23.74  # Total time               : 23.363 s
% 23.46/23.74  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
