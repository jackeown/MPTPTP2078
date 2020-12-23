%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 507 expanded)
%              Number of clauses        :   58 ( 225 expanded)
%              Number of leaves         :   22 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  292 (1340 expanded)
%              Number of equality atoms :  114 ( 628 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t96_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k3_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t111_relat_1,axiom,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(t51_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t168_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k2_relat_1(k7_relat_1(X2,k1_tarski(X1))) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( ( k2_zfmisc_1(X22,X23) != k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X54)
      | k7_relat_1(X54,X53) = k3_xboole_0(X54,k2_zfmisc_1(X53,k2_relat_1(X54))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_relat_1])])).

fof(c_0_25,plain,(
    ! [X32,X33] : v1_relat_1(k2_zfmisc_1(X32,X33)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_30,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | k1_relat_1(k7_relat_1(X52,X51)) = k3_xboole_0(k1_relat_1(X52),X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_31,plain,(
    ! [X35] : k7_relat_1(k1_xboole_0,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t111_relat_1])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X86,X87,X88] :
      ( ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87)))
      | v1_relat_1(X88) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_35,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_37,plain,(
    ! [X26,X27] :
      ( k3_xboole_0(X26,k1_tarski(X27)) != k1_tarski(X27)
      | r2_hidden(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).

cnf(c_0_38,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k7_relat_1(X1,X3))
    | ~ r1_xboole_0(X1,k2_zfmisc_1(X3,k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_43,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_45,plain,(
    ! [X49,X50] :
      ( ( r1_tarski(k1_relat_1(X49),k1_relat_1(X50))
        | ~ r1_tarski(X49,X50)
        | ~ v1_relat_1(X50)
        | ~ v1_relat_1(X49) )
      & ( r1_tarski(k2_relat_1(X49),k2_relat_1(X50))
        | ~ r1_tarski(X49,X50)
        | ~ v1_relat_1(X50)
        | ~ v1_relat_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_46,plain,(
    ! [X44,X45] :
      ( ( k1_relat_1(k2_zfmisc_1(X44,X45)) = X44
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X44,X45)) = X45
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,negated_conjecture,
    ( v1_funct_1(esk14_0)
    & v1_funct_2(esk14_0,k1_tarski(esk12_0),esk13_0)
    & m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk12_0),esk13_0)))
    & esk13_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk12_0),esk13_0,esk14_0) != k1_tarski(k1_funct_1(esk14_0,esk12_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_50,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1))) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k7_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_42]),c_0_44])])).

fof(c_0_55,plain,(
    ! [X89,X90,X91] :
      ( ~ m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90)))
      | k2_relset_1(X89,X90,X91) = k2_relat_1(X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_56,plain,(
    ! [X69,X70,X71] :
      ( ( X71 != k1_funct_1(X69,X70)
        | r2_hidden(k4_tarski(X70,X71),X69)
        | ~ r2_hidden(X70,k1_relat_1(X69))
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( ~ r2_hidden(k4_tarski(X70,X71),X69)
        | X71 = k1_funct_1(X69,X70)
        | ~ r2_hidden(X70,k1_relat_1(X69))
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( X71 != k1_funct_1(X69,X70)
        | X71 = k1_xboole_0
        | r2_hidden(X70,k1_relat_1(X69))
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( X71 != k1_xboole_0
        | X71 = k1_funct_1(X69,X70)
        | r2_hidden(X70,k1_relat_1(X69))
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk12_0),esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | k1_relat_1(k7_relat_1(X2,k1_tarski(X1))) != k1_tarski(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_44]),c_0_43])])).

fof(c_0_64,plain,(
    ! [X97,X98,X99,X100] :
      ( ~ v1_funct_1(X100)
      | ~ v1_funct_2(X100,X97,X98)
      | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))
      | ~ r2_hidden(X99,X97)
      | X98 = k1_xboole_0
      | r2_hidden(k1_funct_1(X100,X99),k2_relset_1(X97,X98,X100)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_65,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_67,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X56)
      | ~ r1_tarski(k1_relat_1(X56),X55)
      | k7_relat_1(X56,X55) = X56 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k1_relat_1(X3),X1)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_32])]),c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk14_0,k2_zfmisc_1(k1_tarski(esk12_0),esk13_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_43]),c_0_42]),c_0_42]),c_0_44])]),c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( esk13_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk12_0),esk13_0,esk14_0) = k2_relat_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk14_0,k1_tarski(esk12_0),esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_76,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_61])).

fof(c_0_78,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk2_2(X19,X20),X20)
        | esk2_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk2_2(X19,X20),X20)
        | esk2_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_79,plain,(
    ! [X24,X25] :
      ( ( ~ r1_tarski(X24,k1_tarski(X25))
        | X24 = k1_xboole_0
        | X24 = k1_tarski(X25) )
      & ( X24 != k1_xboole_0
        | r1_tarski(X24,k1_tarski(X25)) )
      & ( X24 != k1_tarski(X25)
        | r1_tarski(X24,k1_tarski(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

fof(c_0_80,plain,(
    ! [X84,X85] :
      ( ~ v1_relat_1(X85)
      | ~ v1_funct_1(X85)
      | ~ r2_hidden(X84,k1_relat_1(X85))
      | k2_relat_1(k7_relat_1(X85,k1_tarski(X84))) = k1_tarski(k1_funct_1(X85,X84)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_funct_1])])).

cnf(c_0_81,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk14_0),k1_tarski(esk12_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk12_0),esk13_0,esk14_0) != k1_tarski(k1_funct_1(esk14_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk14_0,X1),k2_relat_1(esk14_0))
    | ~ r2_hidden(X1,k1_tarski(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_61]),c_0_73]),c_0_74]),c_0_75])]),c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk14_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_77])])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,plain,
    ( k2_relat_1(k7_relat_1(X1,k1_tarski(X2))) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( k7_relat_1(esk14_0,k1_tarski(esk12_0)) = esk14_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_77])])).

cnf(c_0_90,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk14_0,esk12_0)) != k2_relat_1(esk14_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_73])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk14_0))
    | r2_hidden(X1,k1_relat_1(esk14_0))
    | ~ r2_hidden(X1,k1_tarski(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).

fof(c_0_93,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ r2_hidden(X46,k2_relat_1(X47))
      | r2_hidden(esk4_2(X46,X47),k1_relat_1(X47)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_94,negated_conjecture,
    ( k1_tarski(esk12_0) = k1_relat_1(esk14_0)
    | k1_relat_1(esk14_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(esk12_0,k1_relat_1(esk14_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_75]),c_0_77])]),c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk12_0,k1_relat_1(esk14_0))
    | r2_hidden(k1_xboole_0,k2_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,plain,
    ( r2_hidden(esk4_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k1_relat_1(esk14_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_94]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk14_0)) ),
    inference(sr,[status(thm)],[c_0_96,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk14_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_77])]),c_0_63])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_99,c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.41  fof(t96_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k3_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.41  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.20/0.41  fof(t111_relat_1, axiom, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 0.20/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.20/0.41  fof(t51_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 0.20/0.41  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.41  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.41  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.20/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.41  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.41  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 0.20/0.41  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.41  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.20/0.41  fof(t168_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k2_relat_1(k7_relat_1(X2,k1_tarski(X1)))=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 0.20/0.41  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 0.20/0.41  fof(c_0_22, plain, ![X22, X23]:((k2_zfmisc_1(X22,X23)!=k1_xboole_0|(X22=k1_xboole_0|X23=k1_xboole_0))&((X22!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0)&(X23!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.41  fof(c_0_23, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.41  fof(c_0_24, plain, ![X53, X54]:(~v1_relat_1(X54)|k7_relat_1(X54,X53)=k3_xboole_0(X54,k2_zfmisc_1(X53,k2_relat_1(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_relat_1])])).
% 0.20/0.41  fof(c_0_25, plain, ![X32, X33]:v1_relat_1(k2_zfmisc_1(X32,X33)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  cnf(c_0_26, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_27, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_28, plain, (k7_relat_1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  fof(c_0_29, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.41  fof(c_0_30, plain, ![X51, X52]:(~v1_relat_1(X52)|k1_relat_1(k7_relat_1(X52,X51))=k3_xboole_0(k1_relat_1(X52),X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.20/0.41  fof(c_0_31, plain, ![X35]:k7_relat_1(k1_xboole_0,X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[t111_relat_1])).
% 0.20/0.41  cnf(c_0_32, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_33, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.41  fof(c_0_34, plain, ![X86, X87, X88]:(~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87)))|v1_relat_1(X88)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.41  fof(c_0_35, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.20/0.41  fof(c_0_37, plain, ![X26, X27]:(k3_xboole_0(X26,k1_tarski(X27))!=k1_tarski(X27)|r2_hidden(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_38, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k7_relat_1(X1,X3))|~r1_xboole_0(X1,k2_zfmisc_1(X3,k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_40, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_41, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.41  cnf(c_0_43, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_44, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.41  fof(c_0_45, plain, ![X49, X50]:((r1_tarski(k1_relat_1(X49),k1_relat_1(X50))|~r1_tarski(X49,X50)|~v1_relat_1(X50)|~v1_relat_1(X49))&(r1_tarski(k2_relat_1(X49),k2_relat_1(X50))|~r1_tarski(X49,X50)|~v1_relat_1(X50)|~v1_relat_1(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.41  fof(c_0_46, plain, ![X44, X45]:((k1_relat_1(k2_zfmisc_1(X44,X45))=X44|(X44=k1_xboole_0|X45=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X44,X45))=X45|(X44=k1_xboole_0|X45=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.20/0.41  cnf(c_0_47, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  fof(c_0_49, negated_conjecture, (((v1_funct_1(esk14_0)&v1_funct_2(esk14_0,k1_tarski(esk12_0),esk13_0))&m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk12_0),esk13_0))))&(esk13_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk12_0),esk13_0,esk14_0)!=k1_tarski(k1_funct_1(esk14_0,esk12_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.20/0.41  cnf(c_0_50, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_51, plain, (k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X3,k7_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.41  cnf(c_0_53, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.41  cnf(c_0_54, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_42]), c_0_44])])).
% 0.20/0.41  fof(c_0_55, plain, ![X89, X90, X91]:(~m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90)))|k2_relset_1(X89,X90,X91)=k2_relat_1(X91)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.41  fof(c_0_56, plain, ![X69, X70, X71]:(((X71!=k1_funct_1(X69,X70)|r2_hidden(k4_tarski(X70,X71),X69)|~r2_hidden(X70,k1_relat_1(X69))|(~v1_relat_1(X69)|~v1_funct_1(X69)))&(~r2_hidden(k4_tarski(X70,X71),X69)|X71=k1_funct_1(X69,X70)|~r2_hidden(X70,k1_relat_1(X69))|(~v1_relat_1(X69)|~v1_funct_1(X69))))&((X71!=k1_funct_1(X69,X70)|X71=k1_xboole_0|r2_hidden(X70,k1_relat_1(X69))|(~v1_relat_1(X69)|~v1_funct_1(X69)))&(X71!=k1_xboole_0|X71=k1_funct_1(X69,X70)|r2_hidden(X70,k1_relat_1(X69))|(~v1_relat_1(X69)|~v1_funct_1(X69))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.41  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_58, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.41  cnf(c_0_59, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk12_0),esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_62, plain, (r2_hidden(X1,k1_relat_1(X2))|k1_relat_1(k7_relat_1(X2,k1_tarski(X1)))!=k1_tarski(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_50, c_0_41])).
% 0.20/0.41  cnf(c_0_63, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_44]), c_0_43])])).
% 0.20/0.41  fof(c_0_64, plain, ![X97, X98, X99, X100]:(~v1_funct_1(X100)|~v1_funct_2(X100,X97,X98)|~m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))|(~r2_hidden(X99,X97)|(X98=k1_xboole_0|r2_hidden(k1_funct_1(X100,X99),k2_relset_1(X97,X98,X100))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.20/0.41  cnf(c_0_65, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_66, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  fof(c_0_67, plain, ![X55, X56]:(~v1_relat_1(X56)|(~r1_tarski(k1_relat_1(X56),X55)|k7_relat_1(X56,X55)=X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.41  cnf(c_0_68, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k1_relat_1(X3),X1)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_32])]), c_0_59])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (r1_tarski(esk14_0,k2_zfmisc_1(k1_tarski(esk12_0),esk13_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.41  cnf(c_0_70, plain, (k1_tarski(X1)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_43]), c_0_42]), c_0_42]), c_0_44])]), c_0_63])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (esk13_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_72, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (k2_relset_1(k1_tarski(esk12_0),esk13_0,esk14_0)=k2_relat_1(esk14_0)), inference(spm,[status(thm)],[c_0_65, c_0_61])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk14_0,k1_tarski(esk12_0),esk13_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_76, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (v1_relat_1(esk14_0)), inference(spm,[status(thm)],[c_0_47, c_0_61])).
% 0.20/0.41  fof(c_0_78, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|X17=X15|X16!=k1_tarski(X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_tarski(X15)))&((~r2_hidden(esk2_2(X19,X20),X20)|esk2_2(X19,X20)!=X19|X20=k1_tarski(X19))&(r2_hidden(esk2_2(X19,X20),X20)|esk2_2(X19,X20)=X19|X20=k1_tarski(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.41  fof(c_0_79, plain, ![X24, X25]:((~r1_tarski(X24,k1_tarski(X25))|(X24=k1_xboole_0|X24=k1_tarski(X25)))&((X24!=k1_xboole_0|r1_tarski(X24,k1_tarski(X25)))&(X24!=k1_tarski(X25)|r1_tarski(X24,k1_tarski(X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.20/0.41  fof(c_0_80, plain, ![X84, X85]:(~v1_relat_1(X85)|~v1_funct_1(X85)|(~r2_hidden(X84,k1_relat_1(X85))|k2_relat_1(k7_relat_1(X85,k1_tarski(X84)))=k1_tarski(k1_funct_1(X85,X84)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_funct_1])])).
% 0.20/0.41  cnf(c_0_81, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_relat_1(esk14_0),k1_tarski(esk12_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (k2_relset_1(k1_tarski(esk12_0),esk13_0,esk14_0)!=k1_tarski(k1_funct_1(esk14_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_funct_1(esk14_0,X1),k2_relat_1(esk14_0))|~r2_hidden(X1,k1_tarski(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_61]), c_0_73]), c_0_74]), c_0_75])]), c_0_71])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk14_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_77])])).
% 0.20/0.41  cnf(c_0_86, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.41  cnf(c_0_87, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.41  cnf(c_0_88, plain, (k2_relat_1(k7_relat_1(X1,k1_tarski(X2)))=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (k7_relat_1(esk14_0,k1_tarski(esk12_0))=esk14_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_77])])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (k1_tarski(k1_funct_1(esk14_0,esk12_0))!=k2_relat_1(esk14_0)), inference(rw,[status(thm)],[c_0_83, c_0_73])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (r2_hidden(k1_xboole_0,k2_relat_1(esk14_0))|r2_hidden(X1,k1_relat_1(esk14_0))|~r2_hidden(X1,k1_tarski(esk12_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.41  cnf(c_0_92, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).
% 0.20/0.41  fof(c_0_93, plain, ![X46, X47]:(~v1_relat_1(X47)|(~r2_hidden(X46,k2_relat_1(X47))|r2_hidden(esk4_2(X46,X47),k1_relat_1(X47)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (k1_tarski(esk12_0)=k1_relat_1(esk14_0)|k1_relat_1(esk14_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_82])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (~r2_hidden(esk12_0,k1_relat_1(esk14_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_75]), c_0_77])]), c_0_90])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (r2_hidden(esk12_0,k1_relat_1(esk14_0))|r2_hidden(k1_xboole_0,k2_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.41  cnf(c_0_97, plain, (r2_hidden(esk4_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (k1_relat_1(esk14_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_94]), c_0_95])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (r2_hidden(k1_xboole_0,k2_relat_1(esk14_0))), inference(sr,[status(thm)],[c_0_96, c_0_95])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk14_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_77])]), c_0_63])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_99, c_0_100]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 102
% 0.20/0.41  # Proof object clause steps            : 58
% 0.20/0.41  # Proof object formula steps           : 44
% 0.20/0.41  # Proof object conjectures             : 24
% 0.20/0.41  # Proof object clause conjectures      : 21
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 29
% 0.20/0.41  # Proof object initial formulas used   : 22
% 0.20/0.41  # Proof object generating inferences   : 22
% 0.20/0.41  # Proof object simplifying inferences  : 44
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 33
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 66
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 66
% 0.20/0.41  # Processed clauses                    : 492
% 0.20/0.41  # ...of these trivial                  : 1
% 0.20/0.41  # ...subsumed                          : 202
% 0.20/0.41  # ...remaining for further processing  : 289
% 0.20/0.41  # Other redundant clauses eliminated   : 21
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 5
% 0.20/0.41  # Backward-rewritten                   : 23
% 0.20/0.41  # Generated clauses                    : 967
% 0.20/0.41  # ...of the previous two non-trivial   : 865
% 0.20/0.41  # Contextual simplify-reflections      : 21
% 0.20/0.41  # Paramodulations                      : 946
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 21
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
% 0.20/0.41  # Current number of processed clauses  : 177
% 0.20/0.41  #    Positive orientable unit clauses  : 26
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 6
% 0.20/0.41  #    Non-unit-clauses                  : 145
% 0.20/0.41  # Current number of unprocessed clauses: 502
% 0.20/0.41  # ...number of literals in the above   : 1978
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 96
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 5652
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1938
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 89
% 0.20/0.41  # Unit Clause-clause subsumption calls : 187
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 9
% 0.20/0.41  # BW rewrite match successes           : 8
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 18532
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.055 s
% 0.20/0.41  # System time              : 0.010 s
% 0.20/0.41  # Total time               : 0.065 s
% 0.20/0.41  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
