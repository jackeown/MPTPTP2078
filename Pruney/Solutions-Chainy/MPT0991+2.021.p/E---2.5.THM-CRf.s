%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 200 expanded)
%              Number of clauses        :   45 (  73 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 (1064 expanded)
%              Number of equality atoms :   73 ( 179 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( X2 != k1_xboole_0
          & ? [X4] :
              ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)) )
          & ~ v2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t144_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ~ ( r2_hidden(X2,k2_relat_1(X1))
              & ! [X3] : k10_relat_1(X1,k1_tarski(X2)) != k1_tarski(X3) )
      <=> v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( X2 != k1_xboole_0
            & ? [X4] :
                ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)) )
            & ~ v2_funct_1(X3) ) ) ),
    inference(assume_negation,[status(cth)],[t37_funct_2])).

fof(c_0_18,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X37 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != k1_xboole_0
        | v1_funct_2(X37,X35,X36)
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & esk4_0 != k1_xboole_0
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))
    & ~ v2_funct_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X15,X17,X18] :
      ( ( r2_hidden(esk1_1(X15),k2_relat_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k10_relat_1(X15,k1_tarski(esk1_1(X15))) != k1_tarski(X17)
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ v2_funct_1(X15)
        | ~ r2_hidden(X18,k2_relat_1(X15))
        | k10_relat_1(X15,k1_tarski(X18)) = k1_tarski(esk2_2(X15,X18))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_funct_1])])])])])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X13] :
      ( ( k1_relat_1(X13) != k1_xboole_0
        | k2_relat_1(X13) = k1_xboole_0
        | ~ v1_relat_1(X13) )
      & ( k2_relat_1(X13) != k1_xboole_0
        | k1_relat_1(X13) = k1_xboole_0
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_32,plain,(
    ! [X9,X10] : ~ r2_hidden(X9,k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),k2_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X51] : k6_partfun1(X51) = k6_relat_1(X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_43,plain,(
    ! [X44] :
      ( v1_partfun1(k6_partfun1(X44),X44)
      & m1_subset_1(k6_partfun1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),k2_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r2_relset_1(X31,X32,X33,X34)
        | X33 = X34
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X33 != X34
        | r2_relset_1(X31,X32,X33,X34)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_48,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_54,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_49])).

fof(c_0_57,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ( v1_funct_1(k1_partfun1(X38,X39,X40,X41,X42,X43))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( m1_subset_1(k1_partfun1(X38,X39,X40,X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X38,X41)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_58,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v2_funct_1(k5_relat_1(X21,X20))
      | ~ r1_tarski(k2_relat_1(X21),k1_relat_1(X20))
      | v2_funct_1(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

cnf(c_0_59,negated_conjecture,
    ( k1_relset_1(esk4_0,esk3_0,esk6_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_51]),c_0_52])]),c_0_53])).

fof(c_0_60,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_partfun1(X45,X46,X47,X48,X49,X50) = k5_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_61,negated_conjecture,
    ( k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0) = k6_relat_1(esk3_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_59]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_51])).

cnf(c_0_67,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0) = k6_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_51]),c_0_23]),c_0_63]),c_0_35])])).

fof(c_0_69,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v2_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_70,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_71,negated_conjecture,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,esk6_0))
    | ~ r1_tarski(k2_relat_1(X1),esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_63]),c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk5_0,esk6_0) = k6_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_51]),c_0_23]),c_0_63]),c_0_35])])).

cnf(c_0_73,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_74,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_75,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_35]),c_0_73]),c_0_36])]),c_0_37])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_23])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t37_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2!=k1_xboole_0&?[X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))))&~(v2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 0.19/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.38  fof(t144_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(![X2]:~((r2_hidden(X2,k2_relat_1(X1))&![X3]:k10_relat_1(X1,k1_tarski(X2))!=k1_tarski(X3)))<=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_funct_1)).
% 0.19/0.38  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.38  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.38  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.38  fof(t47_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&r1_tarski(k2_relat_1(X2),k1_relat_1(X1)))=>v2_funct_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 0.19/0.38  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.38  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2!=k1_xboole_0&?[X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))))&~(v2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t37_funct_2])).
% 0.19/0.38  fof(c_0_18, plain, ![X35, X36, X37]:((((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&((~v1_funct_2(X37,X35,X36)|X37=k1_xboole_0|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X37!=k1_xboole_0|v1_funct_2(X37,X35,X36)|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.38  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((esk4_0!=k1_xboole_0&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))))&~v2_funct_1(esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.19/0.38  fof(c_0_20, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  fof(c_0_21, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.38  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_26, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.38  fof(c_0_27, plain, ![X15, X17, X18]:(((r2_hidden(esk1_1(X15),k2_relat_1(X15))|v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(k10_relat_1(X15,k1_tarski(esk1_1(X15)))!=k1_tarski(X17)|v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&(~v2_funct_1(X15)|(~r2_hidden(X18,k2_relat_1(X15))|k10_relat_1(X15,k1_tarski(X18))=k1_tarski(esk2_2(X15,X18)))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_funct_1])])])])])).
% 0.19/0.38  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  fof(c_0_29, plain, ![X13]:((k1_relat_1(X13)!=k1_xboole_0|k2_relat_1(X13)=k1_xboole_0|~v1_relat_1(X13))&(k2_relat_1(X13)!=k1_xboole_0|k1_relat_1(X13)=k1_xboole_0|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.38  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25])).
% 0.19/0.38  fof(c_0_32, plain, ![X9, X10]:~r2_hidden(X9,k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.38  cnf(c_0_33, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),k2_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_38, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_23])])).
% 0.19/0.38  cnf(c_0_40, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_41, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.38  fof(c_0_42, plain, ![X51]:k6_partfun1(X51)=k6_relat_1(X51), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.38  fof(c_0_43, plain, ![X44]:(v1_partfun1(k6_partfun1(X44),X44)&m1_subset_1(k6_partfun1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_1(esk5_0),k2_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_36])])).
% 0.19/0.38  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  fof(c_0_47, plain, ![X31, X32, X33, X34]:((~r2_relset_1(X31,X32,X33,X34)|X33=X34|(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(X33!=X34|r2_relset_1(X31,X32,X33,X34)|(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_49, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_50, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (esk3_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.38  cnf(c_0_54, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.38  cnf(c_0_56, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_50, c_0_49])).
% 0.19/0.38  fof(c_0_57, plain, ![X38, X39, X40, X41, X42, X43]:((v1_funct_1(k1_partfun1(X38,X39,X40,X41,X42,X43))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&(m1_subset_1(k1_partfun1(X38,X39,X40,X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X38,X41)))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.38  fof(c_0_58, plain, ![X20, X21]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v1_relat_1(X21)|~v1_funct_1(X21)|(~v2_funct_1(k5_relat_1(X21,X20))|~r1_tarski(k2_relat_1(X21),k1_relat_1(X20))|v2_funct_1(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k1_relset_1(esk4_0,esk3_0,esk6_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_51]), c_0_52])]), c_0_53])).
% 0.19/0.38  fof(c_0_60, plain, ![X45, X46, X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_partfun1(X45,X46,X47,X48,X49,X50)=k5_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)=k6_relat_1(esk3_0)|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.19/0.38  cnf(c_0_62, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_64, plain, (v2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(k5_relat_1(X2,X1))|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_59]), c_0_51])])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_51])).
% 0.19/0.38  cnf(c_0_67, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)=k6_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_51]), c_0_23]), c_0_63]), c_0_35])])).
% 0.19/0.38  fof(c_0_69, plain, ![X14]:(v1_relat_1(k6_relat_1(X14))&v2_funct_1(k6_relat_1(X14))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.38  fof(c_0_70, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (v2_funct_1(X1)|~v1_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,esk6_0))|~r1_tarski(k2_relat_1(X1),esk4_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_63]), c_0_66])])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk5_0,esk6_0)=k6_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_51]), c_0_23]), c_0_63]), c_0_35])])).
% 0.19/0.38  cnf(c_0_73, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.38  fof(c_0_74, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.38  cnf(c_0_75, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_35]), c_0_73]), c_0_36])]), c_0_37])).
% 0.19/0.38  cnf(c_0_77, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_23])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_36])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 80
% 0.19/0.38  # Proof object clause steps            : 45
% 0.19/0.38  # Proof object formula steps           : 35
% 0.19/0.38  # Proof object conjectures             : 29
% 0.19/0.38  # Proof object clause conjectures      : 26
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 25
% 0.19/0.38  # Proof object initial formulas used   : 17
% 0.19/0.38  # Proof object generating inferences   : 17
% 0.19/0.38  # Proof object simplifying inferences  : 42
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 17
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 41
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 40
% 0.19/0.38  # Processed clauses                    : 129
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 122
% 0.19/0.38  # Other redundant clauses eliminated   : 8
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 2
% 0.19/0.38  # Generated clauses                    : 81
% 0.19/0.38  # ...of the previous two non-trivial   : 72
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 74
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 8
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 72
% 0.19/0.38  #    Positive orientable unit clauses  : 30
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 7
% 0.19/0.38  #    Non-unit-clauses                  : 35
% 0.19/0.38  # Current number of unprocessed clauses: 21
% 0.19/0.38  # ...number of literals in the above   : 102
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 44
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 557
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 137
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.38  # Unit Clause-clause subsumption calls : 45
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4569
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
