%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 406 expanded)
%              Number of clauses        :   77 ( 174 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  358 (1713 expanded)
%              Number of equality atoms :   74 ( 317 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_20,plain,(
    ! [X9] :
      ( X9 = k1_xboole_0
      | r2_hidden(esk2_1(X9),X9) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X18)
      | ~ r1_tarski(X18,X17)
      | ~ r1_xboole_0(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_22,plain,(
    ! [X16] : r1_xboole_0(X16,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X27,X28] :
      ( ( ~ v5_relat_1(X28,X27)
        | r1_tarski(k2_relat_1(X28),X27)
        | ~ v1_relat_1(X28) )
      & ( ~ r1_tarski(k2_relat_1(X28),X27)
        | v5_relat_1(X28,X27)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_30,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_31,plain,(
    ! [X19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_32,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_33,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ( esk4_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk6_0)
      | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_43,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

fof(c_0_46,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_xboole_0(X38)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
      | v1_xboole_0(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_49,plain,(
    ! [X48,X49,X50] :
      ( ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X50 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X50 != k1_xboole_0
        | v1_funct_2(X50,X48,X49)
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_50,plain,(
    ! [X25,X26] :
      ( ( ~ v4_relat_1(X26,X25)
        | r1_tarski(k1_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k1_relat_1(X26),X25)
        | v4_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_54,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

fof(c_0_55,plain,(
    ! [X29,X30,X31] :
      ( ( X31 != k1_funct_1(X29,X30)
        | r2_hidden(k4_tarski(X30,X31),X29)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X29)
        | X31 = k1_funct_1(X29,X30)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 != k1_funct_1(X29,X30)
        | X31 = k1_xboole_0
        | r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 != k1_xboole_0
        | X31 = k1_funct_1(X29,X30)
        | r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_58,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_59,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( v4_relat_1(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_54]),c_0_44]),c_0_45])])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_69,plain,(
    ! [X51,X52] :
      ( ( v1_funct_1(X52)
        | ~ r1_tarski(k2_relat_1(X52),X51)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,k1_relat_1(X52),X51)
        | ~ r1_tarski(k2_relat_1(X52),X51)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),X51)))
        | ~ r1_tarski(k2_relat_1(X52),X51)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_70,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_52]),c_0_60])])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_67])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_68])).

cnf(c_0_78,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_52])])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_82,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
      | ~ r1_tarski(k2_relat_1(X47),X45)
      | m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X45))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0
    | ~ r1_tarski(esk3_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_67])).

cnf(c_0_85,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_52])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_63])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_81])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_80]),c_0_63])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_1(esk6_0)
    | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ r1_tarski(k2_relat_1(esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( v5_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_52])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_91]),c_0_80]),c_0_63])])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk6_0,k1_xboole_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_28])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_67])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_80])])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_36]),c_0_96]),c_0_63])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))
    | ~ r1_tarski(k2_relat_1(esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_89])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_89])).

cnf(c_0_106,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_24]),c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk6_0,k1_xboole_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_48])).

cnf(c_0_108,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_36]),c_0_96]),c_0_63])])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_36]),c_0_96]),c_0_63])])).

cnf(c_0_111,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109])])).

cnf(c_0_113,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112]),c_0_38])])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_109])]),c_0_114]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.41  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.20/0.41  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.41  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.41  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 0.20/0.41  fof(c_0_19, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.41  fof(c_0_20, plain, ![X9]:(X9=k1_xboole_0|r2_hidden(esk2_1(X9),X9)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.41  fof(c_0_21, plain, ![X17, X18]:(v1_xboole_0(X18)|(~r1_tarski(X18,X17)|~r1_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.20/0.41  fof(c_0_22, plain, ![X16]:r1_xboole_0(X16,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.41  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_25, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_27, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_28, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.41  fof(c_0_29, plain, ![X27, X28]:((~v5_relat_1(X28,X27)|r1_tarski(k2_relat_1(X28),X27)|~v1_relat_1(X28))&(~r1_tarski(k2_relat_1(X28),X27)|v5_relat_1(X28,X27)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.41  fof(c_0_30, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.41  fof(c_0_31, plain, ![X19]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.41  fof(c_0_32, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.41  fof(c_0_33, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_34, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.20/0.41  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_37, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_38, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  fof(c_0_40, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  fof(c_0_42, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r1_tarski(esk4_0,esk5_0)&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&(~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.20/0.41  cnf(c_0_43, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.41  cnf(c_0_44, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.41  cnf(c_0_45, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.20/0.41  fof(c_0_46, plain, ![X38, X39, X40]:(~v1_xboole_0(X38)|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))|v1_xboole_0(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.41  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.41  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.41  fof(c_0_49, plain, ![X48, X49, X50]:((((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))))&((~v1_funct_2(X50,X48,X49)|X50=k1_xboole_0|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X50!=k1_xboole_0|v1_funct_2(X50,X48,X49)|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  fof(c_0_50, plain, ![X25, X26]:((~v4_relat_1(X26,X25)|r1_tarski(k1_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k1_relat_1(X26),X25)|v4_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.41  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  fof(c_0_53, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.41  cnf(c_0_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.41  fof(c_0_55, plain, ![X29, X30, X31]:(((X31!=k1_funct_1(X29,X30)|r2_hidden(k4_tarski(X30,X31),X29)|~r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(~r2_hidden(k4_tarski(X30,X31),X29)|X31=k1_funct_1(X29,X30)|~r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((X31!=k1_funct_1(X29,X30)|X31=k1_xboole_0|r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X31!=k1_xboole_0|X31=k1_funct_1(X29,X30)|r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.41  cnf(c_0_56, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.41  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  fof(c_0_58, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k1_relset_1(X41,X42,X43)=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  cnf(c_0_59, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (v4_relat_1(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_52])).
% 0.20/0.41  cnf(c_0_64, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.41  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_54]), c_0_44]), c_0_45])])).
% 0.20/0.41  cnf(c_0_66, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.41  cnf(c_0_68, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.41  fof(c_0_69, plain, ![X51, X52]:(((v1_funct_1(X52)|~r1_tarski(k2_relat_1(X52),X51)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,k1_relat_1(X52),X51)|~r1_tarski(k2_relat_1(X52),X51)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),X51)))|~r1_tarski(k2_relat_1(X52),X51)|(~v1_relat_1(X52)|~v1_funct_1(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.41  cnf(c_0_70, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_52]), c_0_60])])).
% 0.20/0.41  cnf(c_0_72, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.20/0.41  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.41  cnf(c_0_75, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_64, c_0_67])).
% 0.20/0.41  cnf(c_0_77, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_68])).
% 0.20/0.41  cnf(c_0_78, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_52])])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  fof(c_0_82, plain, ![X44, X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|(~r1_tarski(k2_relat_1(X47),X45)|m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X45))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0|~r1_tarski(esk3_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.41  cnf(c_0_84, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_74, c_0_67])).
% 0.20/0.41  cnf(c_0_85, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_75])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_52])).
% 0.20/0.41  cnf(c_0_87, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_28])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_63])])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_81])).
% 0.20/0.41  cnf(c_0_90, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (esk4_0=k1_xboole_0|~r2_hidden(X1,esk3_0)|~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_80]), c_0_63])])).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,esk5_0)|~r1_tarski(k2_relat_1(esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (v5_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_52])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_90, c_0_52])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_91]), c_0_80]), c_0_63])])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(esk6_0,k1_xboole_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_92, c_0_28])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_93, c_0_67])).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_80])])).
% 0.20/0.41  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_36]), c_0_96]), c_0_63])])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))|~r1_tarski(k2_relat_1(esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_97, c_0_89])).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_98, c_0_89])).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (esk3_0=k1_xboole_0|~r1_tarski(esk6_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_24]), c_0_100])).
% 0.20/0.41  cnf(c_0_107, negated_conjecture, (r1_tarski(esk6_0,k1_xboole_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_101, c_0_48])).
% 0.20/0.41  cnf(c_0_108, negated_conjecture, (esk4_0=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.20/0.41  cnf(c_0_109, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_36]), c_0_96]), c_0_63])])).
% 0.20/0.41  cnf(c_0_110, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_36]), c_0_96]), c_0_63])])).
% 0.20/0.41  cnf(c_0_111, negated_conjecture, (esk3_0=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.20/0.41  cnf(c_0_112, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109])])).
% 0.20/0.41  cnf(c_0_113, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_102, c_0_110])).
% 0.20/0.41  cnf(c_0_114, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112]), c_0_38])])).
% 0.20/0.41  cnf(c_0_115, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_109])]), c_0_114]), c_0_38])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 116
% 0.20/0.41  # Proof object clause steps            : 77
% 0.20/0.41  # Proof object formula steps           : 39
% 0.20/0.41  # Proof object conjectures             : 41
% 0.20/0.41  # Proof object clause conjectures      : 38
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 27
% 0.20/0.41  # Proof object initial formulas used   : 19
% 0.20/0.41  # Proof object generating inferences   : 44
% 0.20/0.41  # Proof object simplifying inferences  : 44
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 20
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 42
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 41
% 0.20/0.41  # Processed clauses                    : 589
% 0.20/0.41  # ...of these trivial                  : 1
% 0.20/0.41  # ...subsumed                          : 256
% 0.20/0.41  # ...remaining for further processing  : 331
% 0.20/0.41  # Other redundant clauses eliminated   : 11
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 25
% 0.20/0.41  # Backward-rewritten                   : 139
% 0.20/0.41  # Generated clauses                    : 1048
% 0.20/0.41  # ...of the previous two non-trivial   : 1018
% 0.20/0.41  # Contextual simplify-reflections      : 10
% 0.20/0.41  # Paramodulations                      : 1038
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 11
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 119
% 0.20/0.41  #    Positive orientable unit clauses  : 19
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 100
% 0.20/0.41  # Current number of unprocessed clauses: 478
% 0.20/0.41  # ...number of literals in the above   : 1445
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 203
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 8229
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 6294
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 291
% 0.20/0.41  # Unit Clause-clause subsumption calls : 231
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 18
% 0.20/0.41  # BW rewrite match successes           : 7
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 15523
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.064 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.070 s
% 0.20/0.41  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
