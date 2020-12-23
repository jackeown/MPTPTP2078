%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:37 EST 2020

% Result     : Theorem 15.59s
% Output     : CNFRefutation 15.59s
% Verified   : 
% Statistics : Number of formulae       :  129 (2745 expanded)
%              Number of clauses        :   92 (1324 expanded)
%              Number of leaves         :   18 ( 679 expanded)
%              Depth                    :   19
%              Number of atoms          :  439 (9015 expanded)
%              Number of equality atoms :  106 (2631 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc6_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X2))
         => v5_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(t202_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( r2_hidden(X3,k2_relat_1(X2))
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ( ~ v5_relat_1(X21,X20)
        | r1_tarski(k2_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k2_relat_1(X21),X20)
        | v5_relat_1(X21,X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X52,X53,X54] :
      ( ( v4_relat_1(X54,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( v5_relat_1(X54,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_24,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_25,plain,(
    ! [X22,X23] : v1_relat_1(k2_zfmisc_1(X22,X23)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( X1 = k2_relat_1(X2)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_33,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | v1_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_34,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v5_relat_1(X2,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_35,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k2_relat_1(X1) = k2_relat_1(k1_xboole_0)
    | ~ v5_relat_1(X1,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

fof(c_0_42,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ r1_tarski(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_43,negated_conjecture,(
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

cnf(c_0_44,plain,
    ( k2_relat_1(X1) = k2_relat_1(k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_46,plain,(
    ! [X24,X25,X26,X28] :
      ( ( r2_hidden(esk1_3(X24,X25,X26),k1_relat_1(X26))
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk1_3(X24,X25,X26),X24),X26)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk1_3(X24,X25,X26),X25)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X28,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X28,X24),X26)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_47,negated_conjecture,(
    ! [X70] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ m1_subset_1(X70,esk5_0)
        | ~ r2_hidden(X70,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X70) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_44]),c_0_35]),c_0_36])])).

cnf(c_0_49,plain,
    ( ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_51,plain,(
    ! [X35,X36,X37,X38,X40,X41,X42,X43,X45] :
      ( ( r2_hidden(esk2_4(X35,X36,X37,X38),k1_relat_1(X35))
        | ~ r2_hidden(X38,X37)
        | X37 != k9_relat_1(X35,X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk2_4(X35,X36,X37,X38),X36)
        | ~ r2_hidden(X38,X37)
        | X37 != k9_relat_1(X35,X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X38 = k1_funct_1(X35,esk2_4(X35,X36,X37,X38))
        | ~ r2_hidden(X38,X37)
        | X37 != k9_relat_1(X35,X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X41,k1_relat_1(X35))
        | ~ r2_hidden(X41,X36)
        | X40 != k1_funct_1(X35,X41)
        | r2_hidden(X40,X37)
        | X37 != k9_relat_1(X35,X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(esk3_3(X35,X42,X43),X43)
        | ~ r2_hidden(X45,k1_relat_1(X35))
        | ~ r2_hidden(X45,X42)
        | esk3_3(X35,X42,X43) != k1_funct_1(X35,X45)
        | X43 = k9_relat_1(X35,X42)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk4_3(X35,X42,X43),k1_relat_1(X35))
        | r2_hidden(esk3_3(X35,X42,X43),X43)
        | X43 = k9_relat_1(X35,X42)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk4_3(X35,X42,X43),X42)
        | r2_hidden(esk3_3(X35,X42,X43),X43)
        | X43 = k9_relat_1(X35,X42)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( esk3_3(X35,X42,X43) = k1_funct_1(X35,esk4_3(X35,X42,X43))
        | r2_hidden(esk3_3(X35,X42,X43),X43)
        | X43 = k9_relat_1(X35,X42)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X32,k1_relat_1(X34))
        | ~ r2_hidden(k4_tarski(X32,X33),X34)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(X33,k2_relat_1(X34))
        | ~ r2_hidden(k4_tarski(X32,X33),X34)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_44])).

cnf(c_0_55,plain,
    ( ~ v5_relat_1(X1,esk1_3(X2,k2_relat_1(X1),X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k9_relat_1(X3,k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_52])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_62,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,k2_relat_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_36])])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | r2_hidden(esk4_3(esk8_0,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_61])).

fof(c_0_66,plain,(
    ! [X58,X59,X60,X61] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | k7_relset_1(X58,X59,X60,X61) = k9_relat_1(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,k9_relat_1(X2,k2_relat_1(k1_xboole_0)))
    | r2_hidden(esk3_3(esk8_0,k9_relat_1(X2,k2_relat_1(k1_xboole_0)),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(X1,X2) = k9_relat_1(esk8_0,X3)
    | r2_hidden(esk3_3(esk8_0,X3,k9_relat_1(X1,X2)),k2_relat_1(X1))
    | r2_hidden(esk4_3(esk8_0,X3,k9_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,k2_relat_1(k1_xboole_0))
    | r2_hidden(esk3_3(esk8_0,k2_relat_1(k1_xboole_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_71,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_72,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v5_relat_1(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v5_relat_1(X19,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_75,plain,
    ( esk3_3(X1,X2,X3) = k1_funct_1(X1,esk4_3(X1,X2,X3))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_76,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_77,negated_conjecture,
    ( k9_relat_1(X1,k2_relat_1(k1_xboole_0)) = k9_relat_1(esk8_0,k9_relat_1(X2,k2_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk4_3(esk8_0,X2,k9_relat_1(k1_xboole_0,X1)),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_36]),c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k9_relat_1(esk8_0,k2_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_69])).

fof(c_0_80,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v5_relat_1(X30,X29)
      | ~ r2_hidden(X31,k2_relat_1(X30))
      | r2_hidden(X31,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_52])])).

cnf(c_0_82,plain,
    ( v5_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_74])])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,X1,X2)) = esk3_3(esk8_0,X1,X2)
    | X2 = k9_relat_1(esk8_0,X1)
    | r2_hidden(esk3_3(esk8_0,X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_58])])).

cnf(c_0_87,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk4_3(esk8_0,X2,X1),k1_relat_1(esk8_0))
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_57]),c_0_58])])).

cnf(c_0_88,negated_conjecture,
    ( k9_relat_1(X1,k2_relat_1(k1_xboole_0)) = k9_relat_1(X2,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_78]),c_0_79])).

cnf(c_0_90,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_91,plain,(
    ! [X55,X56,X57] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | k1_relset_1(X55,X56,X57) = k1_relat_1(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_92,plain,
    ( r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_81]),c_0_58])])).

cnf(c_0_94,negated_conjecture,
    ( v5_relat_1(esk8_0,X1)
    | ~ v5_relat_1(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_52]),c_0_30])])).

cnf(c_0_95,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),k9_relat_1(esk8_0,X3))
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | ~ r2_hidden(esk4_3(esk8_0,X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_57]),c_0_58])]),c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k9_relat_1(X1,k2_relat_1(k1_xboole_0)) = k9_relat_1(X2,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_58])).

cnf(c_0_98,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_89])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_35]),c_0_36])])).

cnf(c_0_100,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_101,plain,
    ( k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_90])).

fof(c_0_102,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_103,plain,(
    ! [X62,X63,X64] :
      ( ( ~ v1_funct_2(X64,X62,X63)
        | X62 = k1_relset_1(X62,X63,X64)
        | X63 = k1_xboole_0
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( X62 != k1_relset_1(X62,X63,X64)
        | v1_funct_2(X64,X62,X63)
        | X63 = k1_xboole_0
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( ~ v1_funct_2(X64,X62,X63)
        | X62 = k1_relset_1(X62,X63,X64)
        | X62 != k1_xboole_0
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( X62 != k1_relset_1(X62,X63,X64)
        | v1_funct_2(X64,X62,X63)
        | X62 != k1_xboole_0
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( ~ v1_funct_2(X64,X62,X63)
        | X64 = k1_xboole_0
        | X62 = k1_xboole_0
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( X64 != k1_xboole_0
        | v1_funct_2(X64,X62,X63)
        | X62 = k1_xboole_0
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_104,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | ~ v5_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_58])])).

cnf(c_0_106,negated_conjecture,
    ( v5_relat_1(esk8_0,k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_30])])).

cnf(c_0_107,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),k9_relat_1(esk8_0,X2))
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_63])).

cnf(c_0_108,negated_conjecture,
    ( k9_relat_1(X1,k2_relat_1(k1_xboole_0)) = k9_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_36])])).

cnf(c_0_109,negated_conjecture,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_89]),c_0_29])])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))
    | ~ m1_subset_1(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_57]),c_0_58])])])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_112,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_113,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_114,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_52])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_118,negated_conjecture,
    ( X1 = k9_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk3_3(esk8_0,k2_relat_1(k1_xboole_0),X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_58])]),c_0_109])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)
    | ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_120,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_112])).

cnf(c_0_121,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_113])).

cnf(c_0_122,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_52]),c_0_115]),c_0_116])])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,k2_relat_1(k1_xboole_0),k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0))),k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_109])).

cnf(c_0_124,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_81]),c_0_57]),c_0_58])])).

cnf(c_0_125,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)
    | ~ r2_hidden(X2,k9_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_57]),c_0_58])])).

cnf(c_0_126,negated_conjecture,
    ( ~ v5_relat_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_3(esk8_0,k2_relat_1(k1_xboole_0),k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_123]),c_0_30])])).

cnf(c_0_127,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_81])])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127]),c_0_31]),c_0_127]),c_0_31]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n008.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:35:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 15.59/15.83  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 15.59/15.83  # and selection function SelectMaxLComplexAvoidPosPred.
% 15.59/15.83  #
% 15.59/15.83  # Preprocessing time       : 0.029 s
% 15.59/15.83  
% 15.59/15.83  # Proof found!
% 15.59/15.83  # SZS status Theorem
% 15.59/15.83  # SZS output start CNFRefutation
% 15.59/15.83  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.59/15.83  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 15.59/15.83  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.59/15.83  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.59/15.83  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 15.59/15.83  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.59/15.83  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.59/15.83  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 15.59/15.83  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 15.59/15.83  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 15.59/15.83  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 15.59/15.83  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 15.59/15.83  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 15.59/15.83  fof(cc6_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X2))=>v5_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 15.59/15.83  fof(t202_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(r2_hidden(X3,k2_relat_1(X2))=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 15.59/15.83  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.59/15.83  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 15.59/15.83  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 15.59/15.83  fof(c_0_18, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 15.59/15.83  fof(c_0_19, plain, ![X20, X21]:((~v5_relat_1(X21,X20)|r1_tarski(k2_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_tarski(k2_relat_1(X21),X20)|v5_relat_1(X21,X20)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 15.59/15.83  fof(c_0_20, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 15.59/15.83  cnf(c_0_21, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 15.59/15.83  cnf(c_0_22, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 15.59/15.83  fof(c_0_23, plain, ![X52, X53, X54]:((v4_relat_1(X54,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(v5_relat_1(X54,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 15.59/15.83  fof(c_0_24, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 15.59/15.83  fof(c_0_25, plain, ![X22, X23]:v1_relat_1(k2_zfmisc_1(X22,X23)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 15.59/15.83  cnf(c_0_26, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 15.59/15.83  cnf(c_0_27, plain, (X1=k2_relat_1(X2)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 15.59/15.83  cnf(c_0_28, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 15.59/15.83  cnf(c_0_29, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 15.59/15.83  cnf(c_0_30, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 15.59/15.83  cnf(c_0_31, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 15.59/15.83  cnf(c_0_32, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 15.59/15.83  fof(c_0_33, plain, ![X49, X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|v1_relat_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 15.59/15.83  cnf(c_0_34, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v5_relat_1(X2,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 15.59/15.83  cnf(c_0_35, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 15.59/15.83  cnf(c_0_36, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 15.59/15.83  cnf(c_0_37, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 15.59/15.83  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 15.59/15.83  cnf(c_0_39, plain, (k2_relat_1(X1)=k2_relat_1(k1_xboole_0)|~v5_relat_1(X1,k2_relat_1(k1_xboole_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 15.59/15.83  cnf(c_0_40, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 15.59/15.83  cnf(c_0_41, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 15.59/15.83  fof(c_0_42, plain, ![X47, X48]:(~r2_hidden(X47,X48)|~r1_tarski(X48,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 15.59/15.83  fof(c_0_43, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 15.59/15.83  cnf(c_0_44, plain, (k2_relat_1(X1)=k2_relat_1(k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 15.59/15.83  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 15.59/15.83  fof(c_0_46, plain, ![X24, X25, X26, X28]:((((r2_hidden(esk1_3(X24,X25,X26),k1_relat_1(X26))|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk1_3(X24,X25,X26),X24),X26)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(r2_hidden(esk1_3(X24,X25,X26),X25)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(~r2_hidden(X28,k1_relat_1(X26))|~r2_hidden(k4_tarski(X28,X24),X26)|~r2_hidden(X28,X25)|r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 15.59/15.83  fof(c_0_47, negated_conjecture, ![X70]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~m1_subset_1(X70,esk5_0)|(~r2_hidden(X70,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X70))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).
% 15.59/15.83  cnf(c_0_48, plain, (r1_tarski(k2_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_44]), c_0_35]), c_0_36])])).
% 15.59/15.83  cnf(c_0_49, plain, (~v5_relat_1(X1,X2)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 15.59/15.83  cnf(c_0_50, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 15.59/15.83  fof(c_0_51, plain, ![X35, X36, X37, X38, X40, X41, X42, X43, X45]:(((((r2_hidden(esk2_4(X35,X36,X37,X38),k1_relat_1(X35))|~r2_hidden(X38,X37)|X37!=k9_relat_1(X35,X36)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(r2_hidden(esk2_4(X35,X36,X37,X38),X36)|~r2_hidden(X38,X37)|X37!=k9_relat_1(X35,X36)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(X38=k1_funct_1(X35,esk2_4(X35,X36,X37,X38))|~r2_hidden(X38,X37)|X37!=k9_relat_1(X35,X36)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X41,k1_relat_1(X35))|~r2_hidden(X41,X36)|X40!=k1_funct_1(X35,X41)|r2_hidden(X40,X37)|X37!=k9_relat_1(X35,X36)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&((~r2_hidden(esk3_3(X35,X42,X43),X43)|(~r2_hidden(X45,k1_relat_1(X35))|~r2_hidden(X45,X42)|esk3_3(X35,X42,X43)!=k1_funct_1(X35,X45))|X43=k9_relat_1(X35,X42)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(((r2_hidden(esk4_3(X35,X42,X43),k1_relat_1(X35))|r2_hidden(esk3_3(X35,X42,X43),X43)|X43=k9_relat_1(X35,X42)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(r2_hidden(esk4_3(X35,X42,X43),X42)|r2_hidden(esk3_3(X35,X42,X43),X43)|X43=k9_relat_1(X35,X42)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(esk3_3(X35,X42,X43)=k1_funct_1(X35,esk4_3(X35,X42,X43))|r2_hidden(esk3_3(X35,X42,X43),X43)|X43=k9_relat_1(X35,X42)|(~v1_relat_1(X35)|~v1_funct_1(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 15.59/15.83  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 15.59/15.83  fof(c_0_53, plain, ![X32, X33, X34]:((r2_hidden(X32,k1_relat_1(X34))|~r2_hidden(k4_tarski(X32,X33),X34)|~v1_relat_1(X34))&(r2_hidden(X33,k2_relat_1(X34))|~r2_hidden(k4_tarski(X32,X33),X34)|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 15.59/15.83  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_48, c_0_44])).
% 15.59/15.83  cnf(c_0_55, plain, (~v5_relat_1(X1,esk1_3(X2,k2_relat_1(X1),X3))|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(X2,k9_relat_1(X3,k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 15.59/15.83  cnf(c_0_56, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 15.59/15.83  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_52])).
% 15.59/15.83  cnf(c_0_59, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 15.59/15.83  cnf(c_0_60, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 15.59/15.83  cnf(c_0_61, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 15.59/15.83  cnf(c_0_62, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,k2_relat_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_35]), c_0_36])])).
% 15.59/15.83  cnf(c_0_63, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|r2_hidden(esk4_3(esk8_0,X2,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 15.59/15.83  cnf(c_0_64, plain, (r2_hidden(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 15.59/15.83  cnf(c_0_65, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_45, c_0_61])).
% 15.59/15.83  fof(c_0_66, plain, ![X58, X59, X60, X61]:(~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|k7_relset_1(X58,X59,X60,X61)=k9_relat_1(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 15.59/15.83  cnf(c_0_67, negated_conjecture, (X1=k9_relat_1(esk8_0,k9_relat_1(X2,k2_relat_1(k1_xboole_0)))|r2_hidden(esk3_3(esk8_0,k9_relat_1(X2,k2_relat_1(k1_xboole_0)),X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 15.59/15.83  cnf(c_0_68, negated_conjecture, (k9_relat_1(X1,X2)=k9_relat_1(esk8_0,X3)|r2_hidden(esk3_3(esk8_0,X3,k9_relat_1(X1,X2)),k2_relat_1(X1))|r2_hidden(esk4_3(esk8_0,X3,k9_relat_1(X1,X2)),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_63])).
% 15.59/15.83  cnf(c_0_69, negated_conjecture, (X1=k9_relat_1(esk8_0,k2_relat_1(k1_xboole_0))|r2_hidden(esk3_3(esk8_0,k2_relat_1(k1_xboole_0),X1),X1)), inference(spm,[status(thm)],[c_0_65, c_0_63])).
% 15.59/15.83  cnf(c_0_70, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 15.59/15.83  cnf(c_0_71, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 15.59/15.83  fof(c_0_72, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|~v5_relat_1(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|v5_relat_1(X19,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).
% 15.59/15.83  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 15.59/15.83  cnf(c_0_74, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  cnf(c_0_75, plain, (esk3_3(X1,X2,X3)=k1_funct_1(X1,esk4_3(X1,X2,X3))|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  cnf(c_0_76, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  cnf(c_0_77, negated_conjecture, (k9_relat_1(X1,k2_relat_1(k1_xboole_0))=k9_relat_1(esk8_0,k9_relat_1(X2,k2_relat_1(k1_xboole_0)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_62, c_0_67])).
% 15.59/15.83  cnf(c_0_78, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k9_relat_1(esk8_0,X2)|r2_hidden(esk4_3(esk8_0,X2,k9_relat_1(k1_xboole_0,X1)),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_65])).
% 15.59/15.83  cnf(c_0_79, negated_conjecture, (k9_relat_1(esk8_0,k2_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_69])).
% 15.59/15.83  fof(c_0_80, plain, ![X29, X30, X31]:(~v1_relat_1(X30)|~v5_relat_1(X30,X29)|(~r2_hidden(X31,k2_relat_1(X30))|r2_hidden(X31,X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).
% 15.59/15.83  cnf(c_0_81, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_52])])).
% 15.59/15.83  cnf(c_0_82, plain, (v5_relat_1(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 15.59/15.83  cnf(c_0_83, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 15.59/15.83  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 15.59/15.83  cnf(c_0_85, plain, (r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_74])])).
% 15.59/15.83  cnf(c_0_86, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,X1,X2))=esk3_3(esk8_0,X1,X2)|X2=k9_relat_1(esk8_0,X1)|r2_hidden(esk3_3(esk8_0,X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_57]), c_0_58])])).
% 15.59/15.83  cnf(c_0_87, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk4_3(esk8_0,X2,X1),k1_relat_1(esk8_0))|r2_hidden(esk3_3(esk8_0,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_57]), c_0_58])])).
% 15.59/15.83  cnf(c_0_88, negated_conjecture, (k9_relat_1(X1,k2_relat_1(k1_xboole_0))=k9_relat_1(X2,k2_relat_1(k1_xboole_0))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_77, c_0_77])).
% 15.59/15.83  cnf(c_0_89, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k2_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_78]), c_0_79])).
% 15.59/15.83  cnf(c_0_90, plain, (X1=k1_funct_1(X2,esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  fof(c_0_91, plain, ![X55, X56, X57]:(~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))|k1_relset_1(X55,X56,X57)=k1_relat_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 15.59/15.83  cnf(c_0_92, plain, (r2_hidden(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~r2_hidden(X3,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 15.59/15.83  cnf(c_0_93, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_81]), c_0_58])])).
% 15.59/15.83  cnf(c_0_94, negated_conjecture, (v5_relat_1(esk8_0,X1)|~v5_relat_1(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_52]), c_0_30])])).
% 15.59/15.83  cnf(c_0_95, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 15.59/15.83  cnf(c_0_96, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),k9_relat_1(esk8_0,X3))|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|~r2_hidden(esk4_3(esk8_0,X2,X1),X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_57]), c_0_58])]), c_0_87])).
% 15.59/15.83  cnf(c_0_97, negated_conjecture, (k9_relat_1(X1,k2_relat_1(k1_xboole_0))=k9_relat_1(X2,k2_relat_1(k1_xboole_0))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_88, c_0_58])).
% 15.59/15.83  cnf(c_0_98, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k9_relat_1(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_89, c_0_89])).
% 15.59/15.83  cnf(c_0_99, plain, (~r2_hidden(X1,k2_relat_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_35]), c_0_36])])).
% 15.59/15.83  cnf(c_0_100, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 15.59/15.83  cnf(c_0_101, plain, (k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3))=X3|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_90])).
% 15.59/15.83  fof(c_0_102, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 15.59/15.83  fof(c_0_103, plain, ![X62, X63, X64]:((((~v1_funct_2(X64,X62,X63)|X62=k1_relset_1(X62,X63,X64)|X63=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(X62!=k1_relset_1(X62,X63,X64)|v1_funct_2(X64,X62,X63)|X63=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&((~v1_funct_2(X64,X62,X63)|X62=k1_relset_1(X62,X63,X64)|X62!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(X62!=k1_relset_1(X62,X63,X64)|v1_funct_2(X64,X62,X63)|X62!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&((~v1_funct_2(X64,X62,X63)|X64=k1_xboole_0|X62=k1_xboole_0|X63!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(X64!=k1_xboole_0|v1_funct_2(X64,X62,X63)|X62=k1_xboole_0|X63!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 15.59/15.83  cnf(c_0_104, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 15.59/15.83  cnf(c_0_105, negated_conjecture, (r2_hidden(esk9_0,X1)|~v5_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_58])])).
% 15.59/15.83  cnf(c_0_106, negated_conjecture, (v5_relat_1(esk8_0,k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_30])])).
% 15.59/15.83  cnf(c_0_107, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),k9_relat_1(esk8_0,X2))|r2_hidden(esk3_3(esk8_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_96, c_0_63])).
% 15.59/15.83  cnf(c_0_108, negated_conjecture, (k9_relat_1(X1,k2_relat_1(k1_xboole_0))=k9_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_36])])).
% 15.59/15.83  cnf(c_0_109, negated_conjecture, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_89]), c_0_29])])).
% 15.59/15.83  cnf(c_0_110, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))|~m1_subset_1(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_57]), c_0_58])])])).
% 15.59/15.83  cnf(c_0_111, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 15.59/15.83  cnf(c_0_112, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  cnf(c_0_113, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 15.59/15.83  cnf(c_0_114, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 15.59/15.83  cnf(c_0_115, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_104, c_0_52])).
% 15.59/15.83  cnf(c_0_116, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 15.59/15.83  cnf(c_0_117, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 15.59/15.83  cnf(c_0_118, negated_conjecture, (X1=k9_relat_1(k1_xboole_0,X2)|r2_hidden(esk3_3(esk8_0,k2_relat_1(k1_xboole_0),X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_58])]), c_0_109])).
% 15.59/15.83  cnf(c_0_119, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)|~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 15.59/15.83  cnf(c_0_120, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_112])).
% 15.59/15.83  cnf(c_0_121, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_113])).
% 15.59/15.83  cnf(c_0_122, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_52]), c_0_115]), c_0_116])])).
% 15.59/15.83  cnf(c_0_123, negated_conjecture, (r2_hidden(esk3_3(esk8_0,k2_relat_1(k1_xboole_0),k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0))),k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_109])).
% 15.59/15.83  cnf(c_0_124, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_81]), c_0_57]), c_0_58])])).
% 15.59/15.83  cnf(c_0_125, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)|~r2_hidden(X2,k9_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_57]), c_0_58])])).
% 15.59/15.83  cnf(c_0_126, negated_conjecture, (~v5_relat_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_3(esk8_0,k2_relat_1(k1_xboole_0),k2_relat_1(k2_zfmisc_1(esk5_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_123]), c_0_30])])).
% 15.59/15.83  cnf(c_0_127, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_81])])).
% 15.59/15.83  cnf(c_0_128, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127]), c_0_31]), c_0_127]), c_0_31]), c_0_35])]), ['proof']).
% 15.59/15.83  # SZS output end CNFRefutation
% 15.59/15.83  # Proof object total steps             : 129
% 15.59/15.83  # Proof object clause steps            : 92
% 15.59/15.83  # Proof object formula steps           : 37
% 15.59/15.83  # Proof object conjectures             : 43
% 15.59/15.83  # Proof object clause conjectures      : 40
% 15.59/15.83  # Proof object formula conjectures     : 3
% 15.59/15.83  # Proof object initial clauses used    : 32
% 15.59/15.83  # Proof object initial formulas used   : 18
% 15.59/15.83  # Proof object generating inferences   : 52
% 15.59/15.83  # Proof object simplifying inferences  : 73
% 15.59/15.83  # Training examples: 0 positive, 0 negative
% 15.59/15.83  # Parsed axioms                        : 19
% 15.59/15.83  # Removed by relevancy pruning/SinE    : 0
% 15.59/15.83  # Initial clauses                      : 45
% 15.59/15.83  # Removed in clause preprocessing      : 0
% 15.59/15.83  # Initial clauses in saturation        : 45
% 15.59/15.83  # Processed clauses                    : 46219
% 15.59/15.83  # ...of these trivial                  : 206
% 15.59/15.83  # ...subsumed                          : 41963
% 15.59/15.83  # ...remaining for further processing  : 4050
% 15.59/15.83  # Other redundant clauses eliminated   : 1499
% 15.59/15.83  # Clauses deleted for lack of memory   : 0
% 15.59/15.83  # Backward-subsumed                    : 249
% 15.59/15.83  # Backward-rewritten                   : 1065
% 15.59/15.83  # Generated clauses                    : 1086645
% 15.59/15.83  # ...of the previous two non-trivial   : 1018335
% 15.59/15.83  # Contextual simplify-reflections      : 176
% 15.59/15.83  # Paramodulations                      : 1085096
% 15.59/15.83  # Factorizations                       : 52
% 15.59/15.83  # Equation resolutions                 : 1499
% 15.59/15.83  # Propositional unsat checks           : 0
% 15.59/15.83  #    Propositional check models        : 0
% 15.59/15.83  #    Propositional check unsatisfiable : 0
% 15.59/15.83  #    Propositional clauses             : 0
% 15.59/15.83  #    Propositional clauses after purity: 0
% 15.59/15.83  #    Propositional unsat core size     : 0
% 15.59/15.83  #    Propositional preprocessing time  : 0.000
% 15.59/15.83  #    Propositional encoding time       : 0.000
% 15.59/15.83  #    Propositional solver time         : 0.000
% 15.59/15.83  #    Success case prop preproc time    : 0.000
% 15.59/15.83  #    Success case prop encoding time   : 0.000
% 15.59/15.83  #    Success case prop solver time     : 0.000
% 15.59/15.83  # Current number of processed clauses  : 2724
% 15.59/15.83  #    Positive orientable unit clauses  : 40
% 15.59/15.83  #    Positive unorientable unit clauses: 2
% 15.59/15.83  #    Negative unit clauses             : 14
% 15.59/15.83  #    Non-unit-clauses                  : 2668
% 15.59/15.83  # Current number of unprocessed clauses: 969284
% 15.59/15.83  # ...number of literals in the above   : 5136922
% 15.59/15.83  # Current number of archived formulas  : 0
% 15.59/15.83  # Current number of archived clauses   : 1314
% 15.59/15.83  # Clause-clause subsumption calls (NU) : 1829827
% 15.59/15.83  # Rec. Clause-clause subsumption calls : 643304
% 15.59/15.83  # Non-unit clause-clause subsumptions  : 28715
% 15.59/15.83  # Unit Clause-clause subsumption calls : 9310
% 15.59/15.83  # Rewrite failures with RHS unbound    : 47
% 15.59/15.83  # BW rewrite match attempts            : 122
% 15.59/15.83  # BW rewrite match successes           : 25
% 15.59/15.83  # Condensation attempts                : 0
% 15.59/15.83  # Condensation successes               : 0
% 15.59/15.83  # Termbank termtop insertions          : 24655418
% 15.62/15.87  
% 15.62/15.87  # -------------------------------------------------
% 15.62/15.87  # User time                : 15.026 s
% 15.62/15.87  # System time              : 0.469 s
% 15.62/15.87  # Total time               : 15.495 s
% 15.62/15.87  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
