%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:23 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 273 expanded)
%              Number of clauses        :   73 ( 114 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 (1145 expanded)
%              Number of equality atoms :   66 ( 106 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t172_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(X2))
                     => ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
                      <=> r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t48_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(X2))
                       => ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
                        <=> r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t172_funct_2])).

fof(c_0_24,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)
      | ~ r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0)) )
    & ( r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)
      | r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_26,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_27,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ v1_funct_1(X48)
      | r1_tarski(k9_relat_1(X48,k10_relat_1(X48,X47)),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_28,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_33,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_34,plain,(
    ! [X30] : m1_subset_1(esk2_1(X30),X30) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X65,X66,X67,X68] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | k8_relset_1(X65,X66,X67,X68) = k10_relat_1(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_38,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | v1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_42,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | k1_relset_1(X58,X59,X60) = k1_relat_1(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_43,plain,(
    ! [X69,X70,X71] :
      ( ( k7_relset_1(X69,X70,X71,X69) = k2_relset_1(X69,X70,X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( k8_relset_1(X69,X70,X71,X70) = k1_relset_1(X69,X70,X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_52,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ r1_tarski(X43,X44)
      | r1_tarski(k9_relat_1(X45,X43),k9_relat_1(X45,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

fof(c_0_53,plain,(
    ! [X61,X62,X63,X64] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | k7_relset_1(X61,X62,X63,X64) = k9_relat_1(X63,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_58,plain,(
    ! [X72,X73,X74] :
      ( ( X73 = k1_xboole_0
        | k8_relset_1(X72,X73,X74,X73) = X72
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) )
      & ( X72 != k1_xboole_0
        | k8_relset_1(X72,X73,X74,X73) = X72
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

cnf(c_0_59,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_48])).

fof(c_0_64,plain,(
    ! [X28,X29] :
      ( ( k2_zfmisc_1(X28,X29) != k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ r1_tarski(X1,k9_relat_1(X3,k8_relset_1(X4,X5,X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_66,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)
    | r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_68,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_69,plain,(
    ! [X49,X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ v1_funct_1(X51)
      | ~ r1_tarski(X49,k1_relat_1(X51))
      | ~ r1_tarski(k9_relat_1(X51,X49),X50)
      | r1_tarski(X49,k10_relat_1(X51,X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk3_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_72,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_76,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_63])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)
    | ~ r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_81,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ r1_tarski(X2,k8_relset_1(X4,X5,X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_51])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))
    | r1_tarski(k9_relat_1(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_48])])).

cnf(c_0_83,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk6_0,k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_86,negated_conjecture,
    ( k8_relset_1(esk3_0,esk4_0,esk5_0,esk4_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_48])])).

cnf(c_0_87,plain,
    ( k8_relset_1(X1,X2,X3,X4) = k8_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_50])).

cnf(c_0_88,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_90,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_91,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_79])).

fof(c_0_93,plain,(
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_68]),c_0_48])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_75]),c_0_48])])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,k8_relset_1(X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k9_relat_1(X4,X1),X5)
    | ~ r1_tarski(X1,k1_relat_1(X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_51])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( k8_relset_1(X1,X2,esk5_0,esk4_0) = esk3_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_48])])).

cnf(c_0_99,negated_conjecture,
    ( k10_relat_1(esk5_0,esk4_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_48])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_79]),c_0_90])])).

cnf(c_0_102,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk5_0,k1_xboole_0)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_92])).

cnf(c_0_104,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_105,plain,(
    ! [X25] :
      ( ~ r1_tarski(X25,k1_xboole_0)
      | X25 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk6_0,k8_relset_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k9_relat_1(X3,esk6_0),X4)
    | ~ r1_tarski(esk3_0,k1_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_108,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_98]),c_0_99])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_110,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_111,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_112,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_75]),c_0_48]),c_0_95])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_48])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:29:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 4.31/4.51  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 4.31/4.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.31/4.51  #
% 4.31/4.51  # Preprocessing time       : 0.030 s
% 4.31/4.51  
% 4.31/4.51  # Proof found!
% 4.31/4.51  # SZS status Theorem
% 4.31/4.51  # SZS output start CNFRefutation
% 4.31/4.51  fof(t172_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 4.31/4.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.31/4.51  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.31/4.51  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.31/4.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.31/4.51  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.31/4.51  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.31/4.51  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.31/4.51  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.31/4.51  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.31/4.51  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.31/4.51  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.31/4.51  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.31/4.51  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.31/4.51  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.31/4.51  fof(t48_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 4.31/4.51  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.31/4.51  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.31/4.51  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.31/4.51  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.31/4.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.31/4.51  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.31/4.51  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.31/4.51  fof(c_0_23, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t172_funct_2])).
% 4.31/4.51  fof(c_0_24, plain, ![X34, X35]:((~m1_subset_1(X34,k1_zfmisc_1(X35))|r1_tarski(X34,X35))&(~r1_tarski(X34,X35)|m1_subset_1(X34,k1_zfmisc_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.31/4.51  fof(c_0_25, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)|~r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0)))&(r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)|r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 4.31/4.51  fof(c_0_26, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X22,X23)|r1_tarski(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 4.31/4.51  fof(c_0_27, plain, ![X47, X48]:(~v1_relat_1(X48)|~v1_funct_1(X48)|r1_tarski(k9_relat_1(X48,k10_relat_1(X48,X47)),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 4.31/4.51  fof(c_0_28, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.31/4.51  fof(c_0_29, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 4.31/4.51  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.31/4.51  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  fof(c_0_32, plain, ![X36, X37, X38]:(~r2_hidden(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(X38))|~v1_xboole_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 4.31/4.51  fof(c_0_33, plain, ![X32, X33]:(~m1_subset_1(X32,X33)|(v1_xboole_0(X33)|r2_hidden(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 4.31/4.51  fof(c_0_34, plain, ![X30]:m1_subset_1(esk2_1(X30),X30), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 4.31/4.51  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.31/4.51  cnf(c_0_36, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.31/4.51  fof(c_0_37, plain, ![X65, X66, X67, X68]:(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|k8_relset_1(X65,X66,X67,X68)=k10_relat_1(X67,X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 4.31/4.51  fof(c_0_38, plain, ![X52, X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|v1_relat_1(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 4.31/4.51  cnf(c_0_39, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.31/4.51  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.31/4.51  cnf(c_0_41, negated_conjecture, (r1_tarski(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.31/4.51  fof(c_0_42, plain, ![X58, X59, X60]:(~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|k1_relset_1(X58,X59,X60)=k1_relat_1(X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.31/4.51  fof(c_0_43, plain, ![X69, X70, X71]:((k7_relset_1(X69,X70,X71,X69)=k2_relset_1(X69,X70,X71)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))&(k8_relset_1(X69,X70,X71,X70)=k1_relset_1(X69,X70,X71)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 4.31/4.51  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.31/4.51  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.31/4.51  cnf(c_0_46, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.31/4.51  cnf(c_0_47, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 4.31/4.51  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.31/4.51  cnf(c_0_50, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.31/4.51  cnf(c_0_51, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 4.31/4.51  fof(c_0_52, plain, ![X43, X44, X45]:(~v1_relat_1(X45)|(~r1_tarski(X43,X44)|r1_tarski(k9_relat_1(X45,X43),k9_relat_1(X45,X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 4.31/4.51  fof(c_0_53, plain, ![X61, X62, X63, X64]:(~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))|k7_relset_1(X61,X62,X63,X64)=k9_relat_1(X63,X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 4.31/4.51  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.31/4.51  cnf(c_0_55, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.31/4.51  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 4.31/4.51  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.31/4.51  fof(c_0_58, plain, ![X72, X73, X74]:((X73=k1_xboole_0|k8_relset_1(X72,X73,X74,X73)=X72|(~v1_funct_1(X74)|~v1_funct_2(X74,X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))))&(X72!=k1_xboole_0|k8_relset_1(X72,X73,X74,X73)=X72|(~v1_funct_1(X74)|~v1_funct_2(X74,X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).
% 4.31/4.51  cnf(c_0_59, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 4.31/4.51  cnf(c_0_60, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.31/4.51  cnf(c_0_61, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.31/4.51  cnf(c_0_62, plain, (v1_xboole_0(X1)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 4.31/4.51  cnf(c_0_63, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_48])).
% 4.31/4.51  fof(c_0_64, plain, ![X28, X29]:((k2_zfmisc_1(X28,X29)!=k1_xboole_0|(X28=k1_xboole_0|X29=k1_xboole_0))&((X28!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0)&(X29!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 4.31/4.51  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~r1_tarski(X1,k9_relat_1(X3,k8_relset_1(X4,X5,X3,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 4.31/4.51  cnf(c_0_66, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 4.31/4.51  cnf(c_0_67, negated_conjecture, (r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)|r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  cnf(c_0_68, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 4.31/4.51  fof(c_0_69, plain, ![X49, X50, X51]:(~v1_relat_1(X51)|~v1_funct_1(X51)|(~r1_tarski(X49,k1_relat_1(X51))|~r1_tarski(k9_relat_1(X51,X49),X50)|r1_tarski(X49,k10_relat_1(X51,X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 4.31/4.51  cnf(c_0_70, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 4.31/4.51  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk3_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 4.31/4.51  fof(c_0_72, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.31/4.51  cnf(c_0_73, plain, (X1=k1_xboole_0|k8_relset_1(X2,X1,X3,X1)=X2|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 4.31/4.51  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  cnf(c_0_76, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 4.31/4.51  cnf(c_0_77, plain, (v1_xboole_0(X1)|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 4.31/4.51  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_63])).
% 4.31/4.51  cnf(c_0_79, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 4.31/4.51  cnf(c_0_80, negated_conjecture, (~r1_tarski(k7_relset_1(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)|~r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  cnf(c_0_81, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~r1_tarski(X2,k8_relset_1(X4,X5,X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_51])).
% 4.31/4.51  cnf(c_0_82, negated_conjecture, (r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))|r1_tarski(k9_relat_1(esk5_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_48])])).
% 4.31/4.51  cnf(c_0_83, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 4.31/4.51  cnf(c_0_84, negated_conjecture, (r1_tarski(esk6_0,k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 4.31/4.51  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 4.31/4.51  cnf(c_0_86, negated_conjecture, (k8_relset_1(esk3_0,esk4_0,esk5_0,esk4_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_48])])).
% 4.31/4.51  cnf(c_0_87, plain, (k8_relset_1(X1,X2,X3,X4)=k8_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_50, c_0_50])).
% 4.31/4.51  cnf(c_0_88, plain, (k10_relat_1(X1,X2)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_76])).
% 4.31/4.51  cnf(c_0_89, negated_conjecture, (v1_xboole_0(X1)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 4.31/4.51  cnf(c_0_90, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 4.31/4.51  fof(c_0_91, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.31/4.51  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_79])).
% 4.31/4.51  fof(c_0_93, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 4.31/4.51  cnf(c_0_94, negated_conjecture, (~r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))|~r1_tarski(k9_relat_1(esk5_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_68]), c_0_48])])).
% 4.31/4.51  cnf(c_0_95, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_75]), c_0_48])])).
% 4.31/4.51  cnf(c_0_96, plain, (r1_tarski(X1,k8_relset_1(X2,X3,X4,X5))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k9_relat_1(X4,X1),X5)|~r1_tarski(X1,k1_relat_1(X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_51])).
% 4.31/4.51  cnf(c_0_97, negated_conjecture, (r1_tarski(esk6_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 4.31/4.51  cnf(c_0_98, negated_conjecture, (k8_relset_1(X1,X2,esk5_0,esk4_0)=esk3_0|esk4_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_48])])).
% 4.31/4.51  cnf(c_0_99, negated_conjecture, (k10_relat_1(esk5_0,esk4_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_48])).
% 4.31/4.51  cnf(c_0_100, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.31/4.51  cnf(c_0_101, negated_conjecture, (v1_xboole_0(X1)|esk4_0!=k1_xboole_0|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_79]), c_0_90])])).
% 4.31/4.51  cnf(c_0_102, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 4.31/4.51  cnf(c_0_103, negated_conjecture, (r1_tarski(esk5_0,k1_xboole_0)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_92])).
% 4.31/4.51  cnf(c_0_104, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 4.31/4.51  fof(c_0_105, plain, ![X25]:(~r1_tarski(X25,k1_xboole_0)|X25=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 4.31/4.51  cnf(c_0_106, negated_conjecture, (~r1_tarski(esk6_0,k8_relset_1(esk3_0,esk4_0,esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 4.31/4.51  cnf(c_0_107, negated_conjecture, (r1_tarski(esk6_0,k8_relset_1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k9_relat_1(X3,esk6_0),X4)|~r1_tarski(esk3_0,k1_relat_1(X3))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 4.31/4.51  cnf(c_0_108, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_98]), c_0_99])).
% 4.31/4.51  cnf(c_0_109, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_91])).
% 4.31/4.51  cnf(c_0_110, negated_conjecture, (esk4_0!=k1_xboole_0|~r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 4.31/4.51  cnf(c_0_111, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 4.31/4.51  cnf(c_0_112, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 4.31/4.51  cnf(c_0_113, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_75]), c_0_48]), c_0_95])])).
% 4.31/4.51  cnf(c_0_114, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_48])).
% 4.31/4.51  cnf(c_0_115, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_109])).
% 4.31/4.51  cnf(c_0_116, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])).
% 4.31/4.51  cnf(c_0_117, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])])).
% 4.31/4.51  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117]), c_0_104])]), ['proof']).
% 4.31/4.51  # SZS output end CNFRefutation
% 4.31/4.51  # Proof object total steps             : 119
% 4.31/4.51  # Proof object clause steps            : 73
% 4.31/4.51  # Proof object formula steps           : 46
% 4.31/4.51  # Proof object conjectures             : 37
% 4.31/4.51  # Proof object clause conjectures      : 34
% 4.31/4.51  # Proof object formula conjectures     : 3
% 4.31/4.51  # Proof object initial clauses used    : 33
% 4.31/4.51  # Proof object initial formulas used   : 23
% 4.31/4.51  # Proof object generating inferences   : 37
% 4.31/4.51  # Proof object simplifying inferences  : 33
% 4.31/4.51  # Training examples: 0 positive, 0 negative
% 4.31/4.51  # Parsed axioms                        : 29
% 4.31/4.51  # Removed by relevancy pruning/SinE    : 0
% 4.31/4.51  # Initial clauses                      : 48
% 4.31/4.51  # Removed in clause preprocessing      : 0
% 4.31/4.51  # Initial clauses in saturation        : 48
% 4.31/4.51  # Processed clauses                    : 14487
% 4.31/4.51  # ...of these trivial                  : 94
% 4.31/4.51  # ...subsumed                          : 10072
% 4.31/4.51  # ...remaining for further processing  : 4321
% 4.31/4.51  # Other redundant clauses eliminated   : 2
% 4.31/4.51  # Clauses deleted for lack of memory   : 0
% 4.31/4.51  # Backward-subsumed                    : 391
% 4.31/4.51  # Backward-rewritten                   : 1895
% 4.31/4.51  # Generated clauses                    : 261217
% 4.31/4.51  # ...of the previous two non-trivial   : 252882
% 4.31/4.51  # Contextual simplify-reflections      : 234
% 4.31/4.51  # Paramodulations                      : 261175
% 4.31/4.51  # Factorizations                       : 0
% 4.31/4.51  # Equation resolutions                 : 8
% 4.31/4.51  # Propositional unsat checks           : 0
% 4.31/4.51  #    Propositional check models        : 0
% 4.31/4.51  #    Propositional check unsatisfiable : 0
% 4.31/4.51  #    Propositional clauses             : 0
% 4.31/4.51  #    Propositional clauses after purity: 0
% 4.31/4.51  #    Propositional unsat core size     : 0
% 4.31/4.51  #    Propositional preprocessing time  : 0.000
% 4.31/4.51  #    Propositional encoding time       : 0.000
% 4.31/4.51  #    Propositional solver time         : 0.000
% 4.31/4.51  #    Success case prop preproc time    : 0.000
% 4.31/4.51  #    Success case prop encoding time   : 0.000
% 4.31/4.51  #    Success case prop solver time     : 0.000
% 4.31/4.51  # Current number of processed clauses  : 1999
% 4.31/4.51  #    Positive orientable unit clauses  : 101
% 4.31/4.51  #    Positive unorientable unit clauses: 1
% 4.31/4.51  #    Negative unit clauses             : 5
% 4.31/4.51  #    Non-unit-clauses                  : 1892
% 4.31/4.51  # Current number of unprocessed clauses: 236843
% 4.31/4.51  # ...number of literals in the above   : 1161879
% 4.31/4.51  # Current number of archived formulas  : 0
% 4.31/4.51  # Current number of archived clauses   : 2320
% 4.31/4.51  # Clause-clause subsumption calls (NU) : 1916974
% 4.31/4.51  # Rec. Clause-clause subsumption calls : 767698
% 4.31/4.51  # Non-unit clause-clause subsumptions  : 9032
% 4.31/4.51  # Unit Clause-clause subsumption calls : 10930
% 4.31/4.51  # Rewrite failures with RHS unbound    : 0
% 4.31/4.51  # BW rewrite match attempts            : 967
% 4.31/4.51  # BW rewrite match successes           : 16
% 4.31/4.51  # Condensation attempts                : 0
% 4.31/4.51  # Condensation successes               : 0
% 4.31/4.51  # Termbank termtop insertions          : 4873630
% 4.31/4.53  
% 4.31/4.53  # -------------------------------------------------
% 4.31/4.53  # User time                : 4.046 s
% 4.31/4.53  # System time              : 0.151 s
% 4.31/4.53  # Total time               : 4.197 s
% 4.31/4.53  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
