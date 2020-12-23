%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:56 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  132 (1373 expanded)
%              Number of clauses        :   98 ( 599 expanded)
%              Number of leaves         :   17 ( 339 expanded)
%              Depth                    :   22
%              Number of atoms          :  395 (6509 expanded)
%              Number of equality atoms :  102 (1349 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t142_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(t148_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( v1_partfun1(X3,X1)
              & v1_partfun1(X4,X1)
              & r1_partfun1(X3,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_partfun1(X3,X4)
             => ( ( X2 = k1_xboole_0
                  & X1 != k1_xboole_0 )
                | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_2])).

fof(c_0_18,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X35)))
      | ~ r1_tarski(k2_relat_1(X38),X36)
      | m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_partfun1(esk7_0,esk8_0)
    & ( esk6_0 != k1_xboole_0
      | esk5_0 = k1_xboole_0 )
    & ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_23,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_25,plain,(
    ! [X18] :
      ( m1_subset_1(esk3_1(X18),k1_zfmisc_1(X18))
      & ~ v1_subset_1(esk3_1(X18),X18) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_32,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X48 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X48 != k1_xboole_0
        | v1_funct_2(X48,X46,X47)
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_33,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(pm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(pm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk8_0),X1) ),
    inference(pm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_44,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(pm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(pm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,plain,
    ( r1_tarski(esk3_1(X1),X1) ),
    inference(pm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(pm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk8_0),X1) ),
    inference(pm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_42,c_0_29])).

fof(c_0_54,plain,(
    ! [X43,X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) )
      & ( v1_partfun1(X45,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44,c_0_30]),c_0_45]),c_0_46])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(pm,[status(thm)],[c_0_47,c_0_30])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk3_1(X2)) ),
    inference(pm,[status(thm)],[c_0_48,c_0_50])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_62,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk3_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_51,c_0_37])).

fof(c_0_64,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ v1_funct_1(X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ v1_partfun1(X51,X49)
      | ~ v1_partfun1(X52,X49)
      | ~ r1_partfun1(X51,X52)
      | X51 = X52 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(k2_relat_1(esk8_0)) ),
    inference(pm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk8_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_68,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_42,c_0_59])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_1(esk3_1(X1)),X1)
    | v1_xboole_0(esk3_1(X1)) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_72,plain,
    ( r1_tarski(esk3_1(k2_zfmisc_1(X1,X2)),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_35,c_0_63])).

cnf(c_0_73,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_74,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_partfun1(esk8_0,esk5_0)
    | v1_xboole_0(k2_relat_1(esk8_0))
    | ~ v1_funct_2(esk8_0,esk5_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_57])])).

cnf(c_0_79,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_funct_2(esk8_0,esk5_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68,c_0_56]),c_0_57]),c_0_58])])).

fof(c_0_80,plain,(
    ! [X39,X41,X42] :
      ( ( r2_hidden(esk4_1(X39),X39)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X39)
        | esk4_1(X39) != k4_tarski(X41,X42)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X39)
        | esk4_1(X39) != k4_tarski(X41,X42)
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_81,plain,
    ( v1_xboole_0(esk3_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_82,plain,
    ( v1_xboole_0(esk3_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_83,negated_conjecture,
    ( esk7_0 = X1
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_partfun1(esk7_0,esk5_0)
    | ~ v1_partfun1(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_84,negated_conjecture,
    ( r1_partfun1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk8_0,k1_xboole_0)
    | ~ v1_xboole_0(k2_relat_1(esk8_0)) ),
    inference(pm,[status(thm)],[c_0_35,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_partfun1(esk8_0,esk5_0)
    | v1_xboole_0(k2_relat_1(esk8_0)) ),
    inference(pm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( v1_xboole_0(esk3_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( esk8_0 = esk7_0
    | ~ v1_partfun1(esk7_0,esk5_0)
    | ~ v1_partfun1(esk8_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_30]),c_0_84]),c_0_57])])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_partfun1(esk8_0,esk5_0)
    | r1_tarski(esk8_0,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_42,c_0_87])).

cnf(c_0_93,plain,
    ( v1_xboole_0(esk3_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(pm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_95,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk8_0,k1_xboole_0)
    | ~ v1_partfun1(esk7_0,esk5_0) ),
    inference(pm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_75]),c_0_91]),c_0_76])])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,esk3_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_98,plain,
    ( esk3_1(k1_xboole_0) = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(pm,[status(thm)],[c_0_48,c_0_94])).

cnf(c_0_100,plain,
    ( r2_hidden(esk1_1(X1),X2)
    | v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(pm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_101,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk8_0,k1_xboole_0)
    | v1_xboole_0(esk6_0) ),
    inference(pm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_102,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97,c_0_98]),c_0_73])])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(pm,[status(thm)],[c_0_42,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0
    | v1_xboole_0(esk8_0)
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

fof(c_0_105,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | r2_relset_1(X31,X32,X33,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

cnf(c_0_106,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_41]),c_0_73])])).

cnf(c_0_107,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = esk7_0
    | v1_xboole_0(esk8_0) ),
    inference(pm,[status(thm)],[c_0_92,c_0_104])).

cnf(c_0_108,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_106,c_0_87])).

cnf(c_0_110,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = esk7_0 ),
    inference(pm,[status(thm)],[c_0_92,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(pm,[status(thm)],[c_0_108,c_0_75])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_113,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk8_0 = esk7_0 ),
    inference(pm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0) ),
    inference(pm,[status(thm)],[c_0_111,c_0_30])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(pm,[status(thm)],[c_0_35,c_0_75])).

cnf(c_0_116,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112,c_0_113]),c_0_114])])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(pm,[status(thm)],[c_0_48,c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ v1_partfun1(esk7_0,esk5_0)
    | ~ v1_partfun1(k1_xboole_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_116]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_30]),c_0_46]),c_0_57])])).

cnf(c_0_120,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(pm,[status(thm)],[c_0_42,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_xboole_0(esk6_0)
    | ~ v1_partfun1(k1_xboole_0,esk5_0) ),
    inference(pm,[status(thm)],[c_0_118,c_0_96])).

cnf(c_0_122,negated_conjecture,
    ( v1_partfun1(k1_xboole_0,esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_119,c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_120,c_0_41]),c_0_73])])).

cnf(c_0_124,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_xboole_0(esk6_0) ),
    inference(pm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_123,c_0_87])).

cnf(c_0_126,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_92,c_0_124])).

cnf(c_0_127,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(pm,[status(thm)],[c_0_108,c_0_36])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_112,c_0_116])).

cnf(c_0_129,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_130,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_127,c_0_37])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129]),c_0_130])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.63/1.82  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 1.63/1.82  # and selection function NoSelection.
% 1.63/1.82  #
% 1.63/1.82  # Preprocessing time       : 0.029 s
% 1.63/1.82  
% 1.63/1.82  # Proof found!
% 1.63/1.82  # SZS status Theorem
% 1.63/1.82  # SZS output start CNFRefutation
% 1.63/1.82  fof(t142_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_relset_1(X1,X2,X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 1.63/1.82  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 1.63/1.82  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.63/1.82  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.63/1.82  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.63/1.82  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.63/1.82  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.63/1.82  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 1.63/1.82  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.63/1.82  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.63/1.82  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.63/1.82  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 1.63/1.82  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.63/1.82  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 1.63/1.82  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.82  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 1.63/1.82  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.63/1.82  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_relset_1(X1,X2,X3,X4)))))), inference(assume_negation,[status(cth)],[t142_funct_2])).
% 1.63/1.82  fof(c_0_18, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X35)))|(~r1_tarski(k2_relat_1(X38),X36)|m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X36))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 1.63/1.82  fof(c_0_19, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.63/1.82  fof(c_0_20, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.63/1.82  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r1_partfun1(esk7_0,esk8_0)&((esk6_0!=k1_xboole_0|esk5_0=k1_xboole_0)&~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.63/1.82  fof(c_0_22, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.63/1.82  fof(c_0_23, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.63/1.82  fof(c_0_24, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.63/1.82  fof(c_0_25, plain, ![X18]:(m1_subset_1(esk3_1(X18),k1_zfmisc_1(X18))&~v1_subset_1(esk3_1(X18),X18)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 1.63/1.82  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.82  cnf(c_0_27, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.63/1.82  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.63/1.82  cnf(c_0_29, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.63/1.82  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  fof(c_0_31, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.63/1.82  fof(c_0_32, plain, ![X46, X47, X48]:((((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&((~v1_funct_2(X48,X46,X47)|X48=k1_xboole_0|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X48!=k1_xboole_0|v1_funct_2(X48,X46,X47)|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.63/1.82  cnf(c_0_33, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.63/1.82  fof(c_0_34, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.63/1.82  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.82  cnf(c_0_36, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.63/1.82  cnf(c_0_37, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.63/1.82  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(pm,[status(thm)],[c_0_26, c_0_27])).
% 1.63/1.82  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(pm,[status(thm)],[c_0_28, c_0_29])).
% 1.63/1.82  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r1_tarski(k2_relat_1(esk8_0),X1)), inference(pm,[status(thm)],[c_0_26, c_0_30])).
% 1.63/1.82  cnf(c_0_41, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.63/1.82  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.63/1.82  fof(c_0_43, plain, ![X53]:(((v1_funct_1(X53)|(~v1_relat_1(X53)|~v1_funct_1(X53)))&(v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))|(~v1_relat_1(X53)|~v1_funct_1(X53))))&(m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))|(~v1_relat_1(X53)|~v1_funct_1(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.63/1.82  cnf(c_0_44, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.63/1.82  cnf(c_0_45, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(pm,[status(thm)],[c_0_33, c_0_30])).
% 1.63/1.82  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_47, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.63/1.82  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.63/1.82  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)), inference(pm,[status(thm)],[c_0_35, c_0_36])).
% 1.63/1.82  cnf(c_0_50, plain, (r1_tarski(esk3_1(X1),X1)), inference(pm,[status(thm)],[c_0_35, c_0_37])).
% 1.63/1.82  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(pm,[status(thm)],[c_0_38, c_0_39])).
% 1.63/1.82  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0|~r1_tarski(k2_relat_1(esk8_0),X1)), inference(pm,[status(thm)],[c_0_40, c_0_41])).
% 1.63/1.82  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_42, c_0_29])).
% 1.63/1.82  fof(c_0_54, plain, ![X43, X44, X45]:((v1_funct_1(X45)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))&(v1_partfun1(X45,X43)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 1.63/1.82  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.63/1.82  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44, c_0_30]), c_0_45]), c_0_46])])).
% 1.63/1.82  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk8_0)), inference(pm,[status(thm)],[c_0_47, c_0_30])).
% 1.63/1.82  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(pm,[status(thm)],[c_0_48, c_0_49])).
% 1.63/1.82  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,esk3_1(X2))), inference(pm,[status(thm)],[c_0_48, c_0_50])).
% 1.63/1.82  cnf(c_0_61, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.63/1.82  cnf(c_0_62, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_42, c_0_48])).
% 1.63/1.82  cnf(c_0_63, plain, (m1_subset_1(esk3_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_51, c_0_37])).
% 1.63/1.82  fof(c_0_64, plain, ![X49, X50, X51, X52]:(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(~v1_partfun1(X51,X49)|~v1_partfun1(X52,X49)|~r1_partfun1(X51,X52)|X51=X52))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 1.63/1.82  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0|~v1_xboole_0(k2_relat_1(esk8_0))), inference(pm,[status(thm)],[c_0_52, c_0_53])).
% 1.63/1.82  cnf(c_0_66, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.63/1.82  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk8_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 1.63/1.82  cnf(c_0_68, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.63/1.82  cnf(c_0_69, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_42, c_0_59])).
% 1.63/1.82  cnf(c_0_70, plain, (r2_hidden(esk1_1(esk3_1(X1)),X1)|v1_xboole_0(esk3_1(X1))), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 1.63/1.82  cnf(c_0_71, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_62, c_0_61])).
% 1.63/1.82  cnf(c_0_72, plain, (r1_tarski(esk3_1(k2_zfmisc_1(X1,X2)),k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_35, c_0_63])).
% 1.63/1.82  cnf(c_0_73, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.63/1.82  cnf(c_0_74, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.63/1.82  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_76, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(k2_relat_1(esk8_0))), inference(er,[status(thm)],[c_0_65])).
% 1.63/1.82  cnf(c_0_78, negated_conjecture, (esk6_0=k1_xboole_0|v1_partfun1(esk8_0,esk5_0)|v1_xboole_0(k2_relat_1(esk8_0))|~v1_funct_2(esk8_0,esk5_0,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_57])])).
% 1.63/1.82  cnf(c_0_79, negated_conjecture, (esk6_0=k1_xboole_0|v1_funct_2(esk8_0,esk5_0,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68, c_0_56]), c_0_57]), c_0_58])])).
% 1.63/1.82  fof(c_0_80, plain, ![X39, X41, X42]:((r2_hidden(esk4_1(X39),X39)|X39=k1_xboole_0)&((~r2_hidden(X41,X39)|esk4_1(X39)!=k4_tarski(X41,X42)|X39=k1_xboole_0)&(~r2_hidden(X42,X39)|esk4_1(X39)!=k4_tarski(X41,X42)|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 1.63/1.82  cnf(c_0_81, plain, (v1_xboole_0(esk3_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_69, c_0_70])).
% 1.63/1.82  cnf(c_0_82, plain, (v1_xboole_0(esk3_1(k2_zfmisc_1(X1,X2)))|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 1.63/1.82  cnf(c_0_83, negated_conjecture, (esk7_0=X1|~r1_partfun1(esk7_0,X1)|~v1_partfun1(esk7_0,esk5_0)|~v1_partfun1(X1,esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 1.63/1.82  cnf(c_0_84, negated_conjecture, (r1_partfun1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_85, negated_conjecture, (r1_tarski(esk8_0,k1_xboole_0)|~v1_xboole_0(k2_relat_1(esk8_0))), inference(pm,[status(thm)],[c_0_35, c_0_77])).
% 1.63/1.82  cnf(c_0_86, negated_conjecture, (esk6_0=k1_xboole_0|v1_partfun1(esk8_0,esk5_0)|v1_xboole_0(k2_relat_1(esk8_0))), inference(pm,[status(thm)],[c_0_78, c_0_79])).
% 1.63/1.82  cnf(c_0_87, plain, (r2_hidden(esk4_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.63/1.82  cnf(c_0_88, plain, (v1_xboole_0(esk3_1(k1_xboole_0))|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_81, c_0_82])).
% 1.63/1.82  cnf(c_0_89, negated_conjecture, (esk8_0=esk7_0|~v1_partfun1(esk7_0,esk5_0)|~v1_partfun1(esk8_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_30]), c_0_84]), c_0_57])])).
% 1.63/1.82  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|v1_partfun1(esk8_0,esk5_0)|r1_tarski(esk8_0,k1_xboole_0)), inference(pm,[status(thm)],[c_0_85, c_0_86])).
% 1.63/1.82  cnf(c_0_91, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_92, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_42, c_0_87])).
% 1.63/1.82  cnf(c_0_93, plain, (v1_xboole_0(esk3_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_88])).
% 1.63/1.82  cnf(c_0_94, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(pm,[status(thm)],[c_0_35, c_0_30])).
% 1.63/1.82  cnf(c_0_95, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0|r1_tarski(esk8_0,k1_xboole_0)|~v1_partfun1(esk7_0,esk5_0)), inference(pm,[status(thm)],[c_0_89, c_0_90])).
% 1.63/1.82  cnf(c_0_96, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_75]), c_0_91]), c_0_76])])).
% 1.63/1.82  cnf(c_0_97, plain, (~r2_hidden(X1,esk3_1(X2))|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_62, c_0_50])).
% 1.63/1.82  cnf(c_0_98, plain, (esk3_1(k1_xboole_0)=k1_xboole_0), inference(pm,[status(thm)],[c_0_92, c_0_93])).
% 1.63/1.82  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk8_0)), inference(pm,[status(thm)],[c_0_48, c_0_94])).
% 1.63/1.82  cnf(c_0_100, plain, (r2_hidden(esk1_1(X1),X2)|v1_xboole_0(X1)|~r1_tarski(X1,X2)), inference(pm,[status(thm)],[c_0_48, c_0_61])).
% 1.63/1.82  cnf(c_0_101, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0|r1_tarski(esk8_0,k1_xboole_0)|v1_xboole_0(esk6_0)), inference(pm,[status(thm)],[c_0_95, c_0_96])).
% 1.63/1.82  cnf(c_0_102, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97, c_0_98]), c_0_73])])).
% 1.63/1.82  cnf(c_0_103, negated_conjecture, (~r2_hidden(X1,esk8_0)|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(pm,[status(thm)],[c_0_42, c_0_99])).
% 1.63/1.82  cnf(c_0_104, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0|v1_xboole_0(esk8_0)|v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_100, c_0_101]), c_0_102])).
% 1.63/1.82  fof(c_0_105, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|r2_relset_1(X31,X32,X33,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 1.63/1.82  cnf(c_0_106, negated_conjecture, (esk6_0!=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_41]), c_0_73])])).
% 1.63/1.82  cnf(c_0_107, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=esk7_0|v1_xboole_0(esk8_0)), inference(pm,[status(thm)],[c_0_92, c_0_104])).
% 1.63/1.82  cnf(c_0_108, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 1.63/1.82  cnf(c_0_109, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_106, c_0_87])).
% 1.63/1.82  cnf(c_0_110, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0|esk8_0=esk7_0), inference(pm,[status(thm)],[c_0_92, c_0_107])).
% 1.63/1.82  cnf(c_0_111, negated_conjecture, (r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(pm,[status(thm)],[c_0_108, c_0_75])).
% 1.63/1.82  cnf(c_0_112, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.63/1.82  cnf(c_0_113, negated_conjecture, (esk8_0=k1_xboole_0|esk8_0=esk7_0), inference(pm,[status(thm)],[c_0_109, c_0_110])).
% 1.63/1.82  cnf(c_0_114, negated_conjecture, (r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0)), inference(pm,[status(thm)],[c_0_111, c_0_30])).
% 1.63/1.82  cnf(c_0_115, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(pm,[status(thm)],[c_0_35, c_0_75])).
% 1.63/1.82  cnf(c_0_116, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112, c_0_113]), c_0_114])])).
% 1.63/1.82  cnf(c_0_117, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(pm,[status(thm)],[c_0_48, c_0_115])).
% 1.63/1.82  cnf(c_0_118, negated_conjecture, (esk7_0=k1_xboole_0|~v1_partfun1(esk7_0,esk5_0)|~v1_partfun1(k1_xboole_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_116]), c_0_116])).
% 1.63/1.82  cnf(c_0_119, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_30]), c_0_46]), c_0_57])])).
% 1.63/1.82  cnf(c_0_120, negated_conjecture, (~r2_hidden(X1,esk7_0)|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(pm,[status(thm)],[c_0_42, c_0_117])).
% 1.63/1.82  cnf(c_0_121, negated_conjecture, (esk7_0=k1_xboole_0|v1_xboole_0(esk6_0)|~v1_partfun1(k1_xboole_0,esk5_0)), inference(pm,[status(thm)],[c_0_118, c_0_96])).
% 1.63/1.82  cnf(c_0_122, negated_conjecture, (v1_partfun1(k1_xboole_0,esk5_0)|v1_xboole_0(esk6_0)), inference(rw,[status(thm)],[c_0_119, c_0_116])).
% 1.63/1.82  cnf(c_0_123, negated_conjecture, (esk6_0!=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_120, c_0_41]), c_0_73])])).
% 1.63/1.82  cnf(c_0_124, negated_conjecture, (esk7_0=k1_xboole_0|v1_xboole_0(esk6_0)), inference(pm,[status(thm)],[c_0_121, c_0_122])).
% 1.63/1.82  cnf(c_0_125, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_123, c_0_87])).
% 1.63/1.82  cnf(c_0_126, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(pm,[status(thm)],[c_0_92, c_0_124])).
% 1.63/1.82  cnf(c_0_127, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(pm,[status(thm)],[c_0_108, c_0_36])).
% 1.63/1.82  cnf(c_0_128, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_112, c_0_116])).
% 1.63/1.82  cnf(c_0_129, negated_conjecture, (esk7_0=k1_xboole_0), inference(pm,[status(thm)],[c_0_125, c_0_126])).
% 1.63/1.82  cnf(c_0_130, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(pm,[status(thm)],[c_0_127, c_0_37])).
% 1.63/1.82  cnf(c_0_131, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129]), c_0_130])]), ['proof']).
% 1.63/1.82  # SZS output end CNFRefutation
% 1.63/1.82  # Proof object total steps             : 132
% 1.63/1.82  # Proof object clause steps            : 98
% 1.63/1.82  # Proof object formula steps           : 34
% 1.63/1.82  # Proof object conjectures             : 55
% 1.63/1.82  # Proof object clause conjectures      : 52
% 1.63/1.82  # Proof object formula conjectures     : 3
% 1.63/1.82  # Proof object initial clauses used    : 29
% 1.63/1.82  # Proof object initial formulas used   : 17
% 1.63/1.82  # Proof object generating inferences   : 65
% 1.63/1.82  # Proof object simplifying inferences  : 40
% 1.63/1.82  # Training examples: 0 positive, 0 negative
% 1.63/1.82  # Parsed axioms                        : 18
% 1.63/1.82  # Removed by relevancy pruning/SinE    : 0
% 1.63/1.82  # Initial clauses                      : 43
% 1.63/1.82  # Removed in clause preprocessing      : 2
% 1.63/1.82  # Initial clauses in saturation        : 41
% 1.63/1.82  # Processed clauses                    : 16896
% 1.63/1.82  # ...of these trivial                  : 91
% 1.63/1.82  # ...subsumed                          : 14304
% 1.63/1.82  # ...remaining for further processing  : 2501
% 1.63/1.82  # Other redundant clauses eliminated   : 0
% 1.63/1.82  # Clauses deleted for lack of memory   : 0
% 1.63/1.82  # Backward-subsumed                    : 362
% 1.63/1.82  # Backward-rewritten                   : 1248
% 1.63/1.82  # Generated clauses                    : 196520
% 1.63/1.82  # ...of the previous two non-trivial   : 172255
% 1.63/1.82  # Contextual simplify-reflections      : 0
% 1.63/1.82  # Paramodulations                      : 196511
% 1.63/1.82  # Factorizations                       : 1
% 1.63/1.82  # Equation resolutions                 : 8
% 1.63/1.82  # Propositional unsat checks           : 0
% 1.63/1.82  #    Propositional check models        : 0
% 1.63/1.82  #    Propositional check unsatisfiable : 0
% 1.63/1.82  #    Propositional clauses             : 0
% 1.63/1.82  #    Propositional clauses after purity: 0
% 1.63/1.82  #    Propositional unsat core size     : 0
% 1.63/1.82  #    Propositional preprocessing time  : 0.000
% 1.63/1.82  #    Propositional encoding time       : 0.000
% 1.63/1.82  #    Propositional solver time         : 0.000
% 1.63/1.82  #    Success case prop preproc time    : 0.000
% 1.63/1.82  #    Success case prop encoding time   : 0.000
% 1.63/1.82  #    Success case prop solver time     : 0.000
% 1.63/1.82  # Current number of processed clauses  : 891
% 1.63/1.82  #    Positive orientable unit clauses  : 37
% 1.63/1.82  #    Positive unorientable unit clauses: 0
% 1.63/1.82  #    Negative unit clauses             : 3
% 1.63/1.82  #    Non-unit-clauses                  : 851
% 1.63/1.82  # Current number of unprocessed clauses: 151199
% 1.63/1.82  # ...number of literals in the above   : 701069
% 1.63/1.82  # Current number of archived formulas  : 0
% 1.63/1.82  # Current number of archived clauses   : 1610
% 1.63/1.82  # Clause-clause subsumption calls (NU) : 306364
% 1.63/1.82  # Rec. Clause-clause subsumption calls : 167117
% 1.63/1.82  # Non-unit clause-clause subsumptions  : 12802
% 1.63/1.82  # Unit Clause-clause subsumption calls : 4548
% 1.63/1.82  # Rewrite failures with RHS unbound    : 0
% 1.63/1.82  # BW rewrite match attempts            : 907
% 1.63/1.82  # BW rewrite match successes           : 19
% 1.63/1.82  # Condensation attempts                : 0
% 1.63/1.82  # Condensation successes               : 0
% 1.63/1.82  # Termbank termtop insertions          : 1330865
% 1.67/1.83  
% 1.67/1.83  # -------------------------------------------------
% 1.67/1.83  # User time                : 1.435 s
% 1.67/1.83  # System time              : 0.051 s
% 1.67/1.83  # Total time               : 1.486 s
% 1.67/1.83  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
