%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 333 expanded)
%              Number of clauses        :   63 ( 133 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  375 (1787 expanded)
%              Number of equality atoms :   79 ( 351 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(t185_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(cc6_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & ~ v1_xboole_0(X3)
              & v1_funct_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ! [X5] :
                ( ( v1_funct_1(X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => ( X2 = k1_xboole_0
                        | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_funct_2])).

fof(c_0_20,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | ~ r1_tarski(X35,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_21,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_22,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k1_relset_1(X45,X46,X47) = k1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0)
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk7_0,esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
    & v1_funct_1(esk10_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))
    & m1_subset_1(esk11_0,esk7_0)
    & r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0))
    & esk7_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) != k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ v1_xboole_0(X18)
      | X18 = X19
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k2_relset_1(X48,X49,X50) = k2_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_31,plain,(
    ! [X24,X25,X26,X28,X29,X30,X32] :
      ( ( r2_hidden(esk3_3(X24,X25,X26),k1_relat_1(X24))
        | ~ r2_hidden(X26,X25)
        | X25 != k2_relat_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( X26 = k1_funct_1(X24,esk3_3(X24,X25,X26))
        | ~ r2_hidden(X26,X25)
        | X25 != k2_relat_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(X29,k1_relat_1(X24))
        | X28 != k1_funct_1(X24,X29)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(esk4_2(X24,X30),X30)
        | ~ r2_hidden(X32,k1_relat_1(X24))
        | esk4_2(X24,X30) != k1_funct_1(X24,X32)
        | X30 = k2_relat_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(esk5_2(X24,X30),k1_relat_1(X24))
        | r2_hidden(esk4_2(X24,X30),X30)
        | X30 = k2_relat_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( esk4_2(X24,X30) = k1_funct_1(X24,esk5_2(X24,X30))
        | r2_hidden(esk4_2(X24,X30),X30)
        | X30 = k2_relat_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_32,plain,(
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

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_35,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( k1_relset_1(esk8_0,esk6_0,esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(esk7_0,esk8_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X20,X21)
      | v1_xboole_0(X21)
      | r2_hidden(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_50,plain,(
    ! [X39,X40,X41] :
      ( ( v4_relat_1(X41,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v5_relat_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_51,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk7_0,esk8_0,esk9_0) = k2_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_54,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_33])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_33])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk11_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

fof(c_0_61,plain,(
    ! [X22,X23] :
      ( ( ~ v5_relat_1(X23,X22)
        | r1_tarski(k2_relat_1(X23),X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_tarski(k2_relat_1(X23),X22)
        | v5_relat_1(X23,X22)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_62,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_63,plain,(
    ! [X57,X58,X59] :
      ( ~ v1_relat_1(X58)
      | ~ v5_relat_1(X58,X57)
      | ~ v1_funct_1(X58)
      | ~ r2_hidden(X59,k1_relat_1(X58))
      | k7_partfun1(X57,X58,X59) = k1_funct_1(X58,X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,X1),k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk11_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

fof(c_0_68,plain,(
    ! [X60,X61,X62,X63,X64,X65] :
      ( v1_xboole_0(X62)
      | ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,X61,X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | ~ v1_funct_1(X64)
      | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60)))
      | ~ m1_subset_1(X65,X61)
      | ~ r1_tarski(k2_relset_1(X61,X62,X63),k1_relset_1(X62,X60,X64))
      | X61 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X61,X62,X60,X63,X64),X65) = k1_funct_1(X64,k1_funct_1(X63,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_69,plain,(
    ! [X66,X67] :
      ( ( v1_funct_1(X67)
        | ~ r1_tarski(k2_relat_1(X67),X66)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) )
      & ( v1_funct_2(X67,k1_relat_1(X67),X66)
        | ~ r1_tarski(k2_relat_1(X67),X66)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) )
      & ( m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X67),X66)))
        | ~ r1_tarski(k2_relat_1(X67),X66)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_70,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( v5_relat_1(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

fof(c_0_72,plain,(
    ! [X51,X52,X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X52) )
      & ( ~ v1_xboole_0(X53)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X52) )
      & ( v1_funct_2(X53,X51,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

cnf(c_0_73,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( v5_relat_1(esk10_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_29])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,esk11_0),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_81,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_xboole_0(X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | v1_xboole_0(X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_57])])).

cnf(c_0_84,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( k7_partfun1(esk6_0,esk10_0,X1) = k1_funct_1(esk10_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,esk11_0),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,X1,esk9_0,X2),X3) = k1_funct_1(X2,k1_funct_1(esk9_0,X3))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))
    | ~ m1_subset_1(X3,esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),k1_relset_1(esk8_0,X1,X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_44]),c_0_56]),c_0_33]),c_0_53])]),c_0_35]),c_0_80])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_56]),c_0_57])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_44]),c_0_56]),c_0_33])]),c_0_80]),c_0_60])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) != k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),X1) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_40]),c_0_75]),c_0_29]),c_0_65])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_83])).

cnf(c_0_95,plain,
    ( r2_hidden(k1_funct_1(X1,esk1_1(k1_relat_1(X1))),k2_relat_1(X1))
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_38])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) != k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_59])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk9_0,esk1_1(k1_relat_1(esk9_0))),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_56]),c_0_57])]),c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.46  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.029 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.19/0.46  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.46  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.46  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.46  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.46  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.46  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.46  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.46  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.46  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.46  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.46  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.46  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.19/0.46  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.19/0.46  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.19/0.46  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.19/0.46  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.19/0.46  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.19/0.46  fof(c_0_20, plain, ![X34, X35]:(~r2_hidden(X34,X35)|~r1_tarski(X35,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.46  fof(c_0_21, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.46  fof(c_0_22, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k1_relset_1(X45,X46,X47)=k1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.46  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk8_0)&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&((v1_funct_1(esk10_0)&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0))))&(m1_subset_1(esk11_0,esk7_0)&(r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0))&(esk7_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)!=k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.19/0.46  fof(c_0_24, plain, ![X18, X19]:(~v1_xboole_0(X18)|X18=X19|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.46  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  fof(c_0_27, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.46  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  fof(c_0_30, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k2_relset_1(X48,X49,X50)=k2_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.46  fof(c_0_31, plain, ![X24, X25, X26, X28, X29, X30, X32]:((((r2_hidden(esk3_3(X24,X25,X26),k1_relat_1(X24))|~r2_hidden(X26,X25)|X25!=k2_relat_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(X26=k1_funct_1(X24,esk3_3(X24,X25,X26))|~r2_hidden(X26,X25)|X25!=k2_relat_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))))&(~r2_hidden(X29,k1_relat_1(X24))|X28!=k1_funct_1(X24,X29)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))))&((~r2_hidden(esk4_2(X24,X30),X30)|(~r2_hidden(X32,k1_relat_1(X24))|esk4_2(X24,X30)!=k1_funct_1(X24,X32))|X30=k2_relat_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&((r2_hidden(esk5_2(X24,X30),k1_relat_1(X24))|r2_hidden(esk4_2(X24,X30),X30)|X30=k2_relat_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(esk4_2(X24,X30)=k1_funct_1(X24,esk5_2(X24,X30))|r2_hidden(esk4_2(X24,X30),X30)|X30=k2_relat_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.46  fof(c_0_32, plain, ![X54, X55, X56]:((((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&((~v1_funct_2(X56,X54,X55)|X56=k1_xboole_0|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X56!=k1_xboole_0|v1_funct_2(X56,X54,X55)|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.46  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  fof(c_0_34, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.46  cnf(c_0_35, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_36, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.46  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.46  cnf(c_0_38, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_40, negated_conjecture, (k1_relset_1(esk8_0,esk6_0,esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.46  cnf(c_0_41, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.46  cnf(c_0_42, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_43, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.46  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_45, negated_conjecture, (k1_relset_1(esk7_0,esk8_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.19/0.46  cnf(c_0_46, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.46  fof(c_0_47, plain, ![X20, X21]:(~m1_subset_1(X20,X21)|(v1_xboole_0(X21)|r2_hidden(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.46  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk7_0)|~v1_xboole_0(k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36])])).
% 0.19/0.46  cnf(c_0_49, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.46  fof(c_0_50, plain, ![X39, X40, X41]:((v4_relat_1(X41,X39)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(v5_relat_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.46  fof(c_0_51, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.46  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relat_1(esk10_0))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk7_0,esk8_0,esk9_0)=k2_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 0.19/0.46  cnf(c_0_54, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_33])])).
% 0.19/0.46  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_46, c_0_33])).
% 0.19/0.46  cnf(c_0_58, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk11_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.19/0.46  fof(c_0_61, plain, ![X22, X23]:((~v5_relat_1(X23,X22)|r1_tarski(k2_relat_1(X23),X22)|~v1_relat_1(X23))&(~r1_tarski(k2_relat_1(X23),X22)|v5_relat_1(X23,X22)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.46  cnf(c_0_62, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.46  fof(c_0_63, plain, ![X57, X58, X59]:(~v1_relat_1(X58)|~v5_relat_1(X58,X57)|~v1_funct_1(X58)|(~r2_hidden(X59,k1_relat_1(X58))|k7_partfun1(X57,X58,X59)=k1_funct_1(X58,X59))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.19/0.46  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.46  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),k1_relat_1(esk10_0))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.46  cnf(c_0_66, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,X1),k2_relat_1(esk9_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])])).
% 0.19/0.46  cnf(c_0_67, negated_conjecture, (r2_hidden(esk11_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.46  fof(c_0_68, plain, ![X60, X61, X62, X63, X64, X65]:(v1_xboole_0(X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X61,X62)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))|(~v1_funct_1(X64)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60)))|(~m1_subset_1(X65,X61)|(~r1_tarski(k2_relset_1(X61,X62,X63),k1_relset_1(X62,X60,X64))|(X61=k1_xboole_0|k1_funct_1(k8_funct_2(X61,X62,X60,X63,X64),X65)=k1_funct_1(X64,k1_funct_1(X63,X65)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.19/0.46  fof(c_0_69, plain, ![X66, X67]:(((v1_funct_1(X67)|~r1_tarski(k2_relat_1(X67),X66)|(~v1_relat_1(X67)|~v1_funct_1(X67)))&(v1_funct_2(X67,k1_relat_1(X67),X66)|~r1_tarski(k2_relat_1(X67),X66)|(~v1_relat_1(X67)|~v1_funct_1(X67))))&(m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X67),X66)))|~r1_tarski(k2_relat_1(X67),X66)|(~v1_relat_1(X67)|~v1_funct_1(X67)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.19/0.46  cnf(c_0_70, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.46  cnf(c_0_71, negated_conjecture, (v5_relat_1(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_33])).
% 0.19/0.46  fof(c_0_72, plain, ![X51, X52, X53]:(((v1_funct_1(X53)|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|(v1_xboole_0(X51)|v1_xboole_0(X52)))&(~v1_xboole_0(X53)|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|(v1_xboole_0(X51)|v1_xboole_0(X52))))&(v1_funct_2(X53,X51,X52)|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|(v1_xboole_0(X51)|v1_xboole_0(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.19/0.46  cnf(c_0_73, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.46  cnf(c_0_74, negated_conjecture, (v5_relat_1(esk10_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_29])).
% 0.19/0.46  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_76, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_46, c_0_29])).
% 0.19/0.46  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk10_0))|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.46  cnf(c_0_78, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,esk11_0),k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.46  cnf(c_0_79, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.46  cnf(c_0_80, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  fof(c_0_81, plain, ![X42, X43, X44]:(~v1_xboole_0(X42)|(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|v1_xboole_0(X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.19/0.46  cnf(c_0_82, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.46  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_57])])).
% 0.19/0.46  cnf(c_0_84, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.46  cnf(c_0_85, negated_conjecture, (k7_partfun1(esk6_0,esk10_0,X1)=k1_funct_1(esk10_0,X1)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])])).
% 0.19/0.46  cnf(c_0_86, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,esk11_0),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.46  cnf(c_0_87, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,X1,esk9_0,X2),X3)=k1_funct_1(X2,k1_funct_1(esk9_0,X3))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))|~m1_subset_1(X3,esk7_0)|~r1_tarski(k2_relat_1(esk9_0),k1_relset_1(esk8_0,X1,X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_44]), c_0_56]), c_0_33]), c_0_53])]), c_0_35]), c_0_80])).
% 0.19/0.46  cnf(c_0_88, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.46  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_56]), c_0_57])])).
% 0.19/0.46  cnf(c_0_90, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_44]), c_0_56]), c_0_33])]), c_0_80]), c_0_60])).
% 0.19/0.46  cnf(c_0_91, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)!=k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_92, negated_conjecture, (k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0))=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.46  cnf(c_0_93, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),X1)=k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))|~m1_subset_1(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_40]), c_0_75]), c_0_29]), c_0_65])])).
% 0.19/0.46  cnf(c_0_94, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_64, c_0_83])).
% 0.19/0.46  cnf(c_0_95, plain, (r2_hidden(k1_funct_1(X1,esk1_1(k1_relat_1(X1))),k2_relat_1(X1))|v1_xboole_0(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_38])).
% 0.19/0.46  cnf(c_0_96, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.19/0.46  cnf(c_0_97, negated_conjecture, (esk8_0=k1_xboole_0|k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)!=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.46  cnf(c_0_98, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_93, c_0_59])).
% 0.19/0.46  cnf(c_0_99, negated_conjecture, (r2_hidden(k1_funct_1(esk9_0,esk1_1(k1_relat_1(esk9_0))),esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_56]), c_0_57])]), c_0_96])).
% 0.19/0.46  cnf(c_0_100, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98])])).
% 0.19/0.46  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100]), c_0_37]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 102
% 0.19/0.46  # Proof object clause steps            : 63
% 0.19/0.46  # Proof object formula steps           : 39
% 0.19/0.46  # Proof object conjectures             : 44
% 0.19/0.46  # Proof object clause conjectures      : 41
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 28
% 0.19/0.46  # Proof object initial formulas used   : 19
% 0.19/0.46  # Proof object generating inferences   : 29
% 0.19/0.46  # Proof object simplifying inferences  : 46
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 19
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 47
% 0.19/0.46  # Removed in clause preprocessing      : 3
% 0.19/0.46  # Initial clauses in saturation        : 44
% 0.19/0.46  # Processed clauses                    : 1488
% 0.19/0.46  # ...of these trivial                  : 3
% 0.19/0.46  # ...subsumed                          : 1047
% 0.19/0.46  # ...remaining for further processing  : 438
% 0.19/0.46  # Other redundant clauses eliminated   : 144
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 11
% 0.19/0.46  # Backward-rewritten                   : 200
% 0.19/0.46  # Generated clauses                    : 2852
% 0.19/0.46  # ...of the previous two non-trivial   : 2674
% 0.19/0.46  # Contextual simplify-reflections      : 1
% 0.19/0.46  # Paramodulations                      : 2709
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 145
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 176
% 0.19/0.46  #    Positive orientable unit clauses  : 27
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 9
% 0.19/0.46  #    Non-unit-clauses                  : 140
% 0.19/0.46  # Current number of unprocessed clauses: 1207
% 0.19/0.46  # ...number of literals in the above   : 6699
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 255
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 27036
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 5403
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 688
% 0.19/0.46  # Unit Clause-clause subsumption calls : 319
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 30
% 0.19/0.46  # BW rewrite match successes           : 6
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 50031
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.121 s
% 0.19/0.46  # System time              : 0.007 s
% 0.19/0.46  # Total time               : 0.129 s
% 0.19/0.46  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
