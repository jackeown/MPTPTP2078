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
% DateTime   : Thu Dec  3 11:06:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 474 expanded)
%              Number of clauses        :   73 ( 241 expanded)
%              Number of leaves         :   16 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  403 (3621 expanded)
%              Number of equality atoms :   68 (1285 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

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

fof(c_0_16,plain,(
    ! [X56,X57,X58,X59,X61,X62,X63,X64,X65,X67] :
      ( ( v1_relat_1(esk6_4(X56,X57,X58,X59))
        | ~ r2_hidden(X59,X58)
        | X58 != k1_funct_2(X56,X57) )
      & ( v1_funct_1(esk6_4(X56,X57,X58,X59))
        | ~ r2_hidden(X59,X58)
        | X58 != k1_funct_2(X56,X57) )
      & ( X59 = esk6_4(X56,X57,X58,X59)
        | ~ r2_hidden(X59,X58)
        | X58 != k1_funct_2(X56,X57) )
      & ( k1_relat_1(esk6_4(X56,X57,X58,X59)) = X56
        | ~ r2_hidden(X59,X58)
        | X58 != k1_funct_2(X56,X57) )
      & ( r1_tarski(k2_relat_1(esk6_4(X56,X57,X58,X59)),X57)
        | ~ r2_hidden(X59,X58)
        | X58 != k1_funct_2(X56,X57) )
      & ( ~ v1_relat_1(X62)
        | ~ v1_funct_1(X62)
        | X61 != X62
        | k1_relat_1(X62) != X56
        | ~ r1_tarski(k2_relat_1(X62),X57)
        | r2_hidden(X61,X58)
        | X58 != k1_funct_2(X56,X57) )
      & ( ~ r2_hidden(esk7_3(X63,X64,X65),X65)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67)
        | esk7_3(X63,X64,X65) != X67
        | k1_relat_1(X67) != X63
        | ~ r1_tarski(k2_relat_1(X67),X64)
        | X65 = k1_funct_2(X63,X64) )
      & ( v1_relat_1(esk8_3(X63,X64,X65))
        | r2_hidden(esk7_3(X63,X64,X65),X65)
        | X65 = k1_funct_2(X63,X64) )
      & ( v1_funct_1(esk8_3(X63,X64,X65))
        | r2_hidden(esk7_3(X63,X64,X65),X65)
        | X65 = k1_funct_2(X63,X64) )
      & ( esk7_3(X63,X64,X65) = esk8_3(X63,X64,X65)
        | r2_hidden(esk7_3(X63,X64,X65),X65)
        | X65 = k1_funct_2(X63,X64) )
      & ( k1_relat_1(esk8_3(X63,X64,X65)) = X63
        | r2_hidden(esk7_3(X63,X64,X65),X65)
        | X65 = k1_funct_2(X63,X64) )
      & ( r1_tarski(k2_relat_1(esk8_3(X63,X64,X65)),X64)
        | r2_hidden(esk7_3(X63,X64,X65),X65)
        | X65 = k1_funct_2(X63,X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X44,X45,X46,X47] :
      ( ( X44 = k4_tarski(esk4_4(X44,X45,X46,X47),esk5_4(X44,X45,X46,X47))
        | ~ r2_hidden(X44,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( r2_hidden(esk4_4(X44,X45,X46,X47),X45)
        | ~ r2_hidden(X44,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( r2_hidden(esk5_4(X44,X45,X46,X47),X46)
        | ~ r2_hidden(X44,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

cnf(c_0_20,plain,
    ( k1_relat_1(esk6_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = esk6_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_23,plain,
    ( v1_funct_1(esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( k1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( esk6_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_32,negated_conjecture,
    ( r2_hidden(esk12_0,k1_funct_2(esk10_0,esk11_0))
    & ( ~ v1_funct_1(esk12_0)
      | ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
      | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_33,plain,
    ( v1_funct_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_40,plain,(
    ! [X69] :
      ( ( v1_funct_1(X69)
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( v1_funct_2(X69,k1_relat_1(X69),k2_relat_1(X69))
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) )
      & ( m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X69),k2_relat_1(X69))))
        | ~ v1_relat_1(X69)
        | ~ v1_funct_1(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk12_0,k1_funct_2(esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk12_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

fof(c_0_52,plain,(
    ! [X70,X71,X72] :
      ( ( v1_funct_1(X72)
        | r2_hidden(esk9_3(X70,X71,X72),X70)
        | k1_relat_1(X72) != X70
        | ~ v1_relat_1(X72)
        | ~ v1_funct_1(X72) )
      & ( v1_funct_2(X72,X70,X71)
        | r2_hidden(esk9_3(X70,X71,X72),X70)
        | k1_relat_1(X72) != X70
        | ~ v1_relat_1(X72)
        | ~ v1_funct_1(X72) )
      & ( m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | r2_hidden(esk9_3(X70,X71,X72),X70)
        | k1_relat_1(X72) != X70
        | ~ v1_relat_1(X72)
        | ~ v1_funct_1(X72) )
      & ( v1_funct_1(X72)
        | ~ r2_hidden(k1_funct_1(X72,esk9_3(X70,X71,X72)),X71)
        | k1_relat_1(X72) != X70
        | ~ v1_relat_1(X72)
        | ~ v1_funct_1(X72) )
      & ( v1_funct_2(X72,X70,X71)
        | ~ r2_hidden(k1_funct_1(X72,esk9_3(X70,X71,X72)),X71)
        | k1_relat_1(X72) != X70
        | ~ v1_relat_1(X72)
        | ~ v1_funct_1(X72) )
      & ( m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ r2_hidden(k1_funct_1(X72,esk9_3(X70,X71,X72)),X71)
        | k1_relat_1(X72) != X70
        | ~ v1_relat_1(X72)
        | ~ v1_funct_1(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

fof(c_0_53,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_1(esk12_0)
    | ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_59,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_tarski(k1_relat_1(X39),X37)
      | ~ r1_tarski(k2_relat_1(X39),X38)
      | m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,k2_relat_1(esk12_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_61,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(k1_funct_1(X1,esk9_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_62,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v5_relat_1(X26,X25)
      | ~ v1_funct_1(X26)
      | ~ r2_hidden(X27,k1_relat_1(X26))
      | r2_hidden(k1_funct_1(X26,X27),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_63,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk9_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_64,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_50])])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ v1_funct_1(esk12_0)
    | ~ r1_tarski(esk12_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk12_0)
    | ~ v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_72,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,esk9_3(k1_relat_1(X1),X2,X1)),X2) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk9_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ v1_relat_1(esk12_0)
    | ~ r1_tarski(k1_relat_1(esk12_0),esk10_0)
    | ~ r1_tarski(k2_relat_1(esk12_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_79,plain,(
    ! [X50,X51,X52] :
      ( ( v1_funct_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_partfun1(X52,X50)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( v1_funct_2(X52,X50,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_partfun1(X52,X50)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_80,plain,(
    ! [X53,X54,X55] :
      ( ( v1_funct_1(X55)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | v1_xboole_0(X54) )
      & ( v1_partfun1(X55,X53)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | v1_xboole_0(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_81,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ r1_tarski(esk12_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_50])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk12_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_27])).

cnf(c_0_84,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_85,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ r1_tarski(k1_relat_1(esk12_0),esk10_0)
    | ~ r1_tarski(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_51])])).

cnf(c_0_88,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk12_0,esk10_0,k2_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(esk12_0,esk10_0,X1)
    | ~ v5_relat_1(esk12_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_93,negated_conjecture,
    ( v5_relat_1(esk12_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,plain,
    ( r1_tarski(k2_relat_1(esk6_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(esk12_0,esk10_0,esk11_0)
    | ~ r1_tarski(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_49]),c_0_47])])).

cnf(c_0_96,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_88,c_0_69])).

cnf(c_0_97,negated_conjecture,
    ( v1_partfun1(esk12_0,esk10_0)
    | v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_60]),c_0_90]),c_0_50])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk12_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_99,plain,
    ( r1_tarski(k2_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_partfun1(esk12_0,esk10_0)
    | ~ r1_tarski(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_50]),c_0_51]),c_0_49]),c_0_47])])).

cnf(c_0_101,negated_conjecture,
    ( v1_partfun1(esk12_0,esk10_0) ),
    inference(sr,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_31])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_42]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.030 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.50  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 0.20/0.50  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.50  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.50  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.50  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.50  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.50  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 0.20/0.50  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.50  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.50  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.50  fof(c_0_16, plain, ![X56, X57, X58, X59, X61, X62, X63, X64, X65, X67]:(((((((v1_relat_1(esk6_4(X56,X57,X58,X59))|~r2_hidden(X59,X58)|X58!=k1_funct_2(X56,X57))&(v1_funct_1(esk6_4(X56,X57,X58,X59))|~r2_hidden(X59,X58)|X58!=k1_funct_2(X56,X57)))&(X59=esk6_4(X56,X57,X58,X59)|~r2_hidden(X59,X58)|X58!=k1_funct_2(X56,X57)))&(k1_relat_1(esk6_4(X56,X57,X58,X59))=X56|~r2_hidden(X59,X58)|X58!=k1_funct_2(X56,X57)))&(r1_tarski(k2_relat_1(esk6_4(X56,X57,X58,X59)),X57)|~r2_hidden(X59,X58)|X58!=k1_funct_2(X56,X57)))&(~v1_relat_1(X62)|~v1_funct_1(X62)|X61!=X62|k1_relat_1(X62)!=X56|~r1_tarski(k2_relat_1(X62),X57)|r2_hidden(X61,X58)|X58!=k1_funct_2(X56,X57)))&((~r2_hidden(esk7_3(X63,X64,X65),X65)|(~v1_relat_1(X67)|~v1_funct_1(X67)|esk7_3(X63,X64,X65)!=X67|k1_relat_1(X67)!=X63|~r1_tarski(k2_relat_1(X67),X64))|X65=k1_funct_2(X63,X64))&(((((v1_relat_1(esk8_3(X63,X64,X65))|r2_hidden(esk7_3(X63,X64,X65),X65)|X65=k1_funct_2(X63,X64))&(v1_funct_1(esk8_3(X63,X64,X65))|r2_hidden(esk7_3(X63,X64,X65),X65)|X65=k1_funct_2(X63,X64)))&(esk7_3(X63,X64,X65)=esk8_3(X63,X64,X65)|r2_hidden(esk7_3(X63,X64,X65),X65)|X65=k1_funct_2(X63,X64)))&(k1_relat_1(esk8_3(X63,X64,X65))=X63|r2_hidden(esk7_3(X63,X64,X65),X65)|X65=k1_funct_2(X63,X64)))&(r1_tarski(k2_relat_1(esk8_3(X63,X64,X65)),X64)|r2_hidden(esk7_3(X63,X64,X65),X65)|X65=k1_funct_2(X63,X64))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.50  fof(c_0_17, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.50  fof(c_0_18, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.50  fof(c_0_19, plain, ![X44, X45, X46, X47]:(((X44=k4_tarski(esk4_4(X44,X45,X46,X47),esk5_4(X44,X45,X46,X47))|~r2_hidden(X44,X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(r2_hidden(esk4_4(X44,X45,X46,X47),X45)|~r2_hidden(X44,X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(r2_hidden(esk5_4(X44,X45,X46,X47),X46)|~r2_hidden(X44,X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 0.20/0.50  cnf(c_0_20, plain, (k1_relat_1(esk6_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_21, plain, (X1=esk6_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.20/0.50  cnf(c_0_23, plain, (v1_funct_1(esk6_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_24, plain, (v1_relat_1(esk6_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  fof(c_0_25, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.50  cnf(c_0_27, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.50  cnf(c_0_28, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  fof(c_0_29, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.50  cnf(c_0_30, plain, (k1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_31, plain, (esk6_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.50  fof(c_0_32, negated_conjecture, (r2_hidden(esk12_0,k1_funct_2(esk10_0,esk11_0))&(~v1_funct_1(esk12_0)|~v1_funct_2(esk12_0,esk10_0,esk11_0)|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.20/0.50  cnf(c_0_33, plain, (v1_funct_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.50  cnf(c_0_34, plain, (v1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.50  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.50  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.50  cnf(c_0_37, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.20/0.50  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.50  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.50  fof(c_0_40, plain, ![X69]:(((v1_funct_1(X69)|(~v1_relat_1(X69)|~v1_funct_1(X69)))&(v1_funct_2(X69,k1_relat_1(X69),k2_relat_1(X69))|(~v1_relat_1(X69)|~v1_funct_1(X69))))&(m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X69),k2_relat_1(X69))))|(~v1_relat_1(X69)|~v1_funct_1(X69)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.50  cnf(c_0_41, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.50  cnf(c_0_42, negated_conjecture, (r2_hidden(esk12_0,k1_funct_2(esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.50  cnf(c_0_43, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.20/0.50  cnf(c_0_44, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.20/0.50  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.50  cnf(c_0_46, plain, (~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.50  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.50  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk12_0)=esk10_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.50  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk12_0)), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk12_0)), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.20/0.50  fof(c_0_52, plain, ![X70, X71, X72]:((((v1_funct_1(X72)|(r2_hidden(esk9_3(X70,X71,X72),X70)|k1_relat_1(X72)!=X70)|(~v1_relat_1(X72)|~v1_funct_1(X72)))&(v1_funct_2(X72,X70,X71)|(r2_hidden(esk9_3(X70,X71,X72),X70)|k1_relat_1(X72)!=X70)|(~v1_relat_1(X72)|~v1_funct_1(X72))))&(m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|(r2_hidden(esk9_3(X70,X71,X72),X70)|k1_relat_1(X72)!=X70)|(~v1_relat_1(X72)|~v1_funct_1(X72))))&(((v1_funct_1(X72)|(~r2_hidden(k1_funct_1(X72,esk9_3(X70,X71,X72)),X71)|k1_relat_1(X72)!=X70)|(~v1_relat_1(X72)|~v1_funct_1(X72)))&(v1_funct_2(X72,X70,X71)|(~r2_hidden(k1_funct_1(X72,esk9_3(X70,X71,X72)),X71)|k1_relat_1(X72)!=X70)|(~v1_relat_1(X72)|~v1_funct_1(X72))))&(m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|(~r2_hidden(k1_funct_1(X72,esk9_3(X70,X71,X72)),X71)|k1_relat_1(X72)!=X70)|(~v1_relat_1(X72)|~v1_funct_1(X72))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.50  fof(c_0_53, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.50  cnf(c_0_54, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.20/0.50  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.50  cnf(c_0_56, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.50  cnf(c_0_57, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (~v1_funct_1(esk12_0)|~v1_funct_2(esk12_0,esk10_0,esk11_0)|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.50  fof(c_0_59, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|(~r1_tarski(k1_relat_1(X39),X37)|~r1_tarski(k2_relat_1(X39),X38)|m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,k2_relat_1(esk12_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])])).
% 0.20/0.50  cnf(c_0_61, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(k1_funct_1(X1,esk9_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.50  fof(c_0_62, plain, ![X25, X26, X27]:(~v1_relat_1(X26)|~v5_relat_1(X26,X25)|~v1_funct_1(X26)|(~r2_hidden(X27,k1_relat_1(X26))|r2_hidden(k1_funct_1(X26,X27),X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.20/0.50  cnf(c_0_63, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk9_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.50  fof(c_0_64, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.50  cnf(c_0_65, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.50  cnf(c_0_66, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.50  cnf(c_0_67, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.50  cnf(c_0_68, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_50])])).
% 0.20/0.50  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.50  cnf(c_0_70, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~v1_funct_1(esk12_0)|~r1_tarski(esk12_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_58, c_0_38])).
% 0.20/0.50  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk12_0)|~v1_xboole_0(k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 0.20/0.50  cnf(c_0_72, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,esk9_3(k1_relat_1(X1),X2,X1)),X2)), inference(er,[status(thm)],[c_0_61])).
% 0.20/0.50  cnf(c_0_73, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.50  cnf(c_0_74, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk9_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_63])).
% 0.20/0.50  cnf(c_0_75, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.50  cnf(c_0_76, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_65])).
% 0.20/0.50  cnf(c_0_77, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.50  cnf(c_0_78, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~v1_relat_1(esk12_0)|~r1_tarski(k1_relat_1(esk12_0),esk10_0)|~r1_tarski(k2_relat_1(esk12_0),esk11_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.50  fof(c_0_79, plain, ![X50, X51, X52]:((v1_funct_1(X52)|(~v1_funct_1(X52)|~v1_partfun1(X52,X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(v1_funct_2(X52,X50,X51)|(~v1_funct_1(X52)|~v1_partfun1(X52,X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.50  fof(c_0_80, plain, ![X53, X54, X55]:((v1_funct_1(X55)|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|v1_xboole_0(X54))&(v1_partfun1(X55,X53)|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|v1_xboole_0(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.50  cnf(c_0_81, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_82, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~r1_tarski(esk12_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_50])])).
% 0.20/0.50  cnf(c_0_83, negated_conjecture, (r1_tarski(esk12_0,X1)|~v1_xboole_0(k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_71, c_0_27])).
% 0.20/0.50  cnf(c_0_84, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~v1_funct_1(X1)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.20/0.50  cnf(c_0_85, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.50  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_60, c_0_77])).
% 0.20/0.50  cnf(c_0_87, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~r1_tarski(k1_relat_1(esk12_0),esk10_0)|~r1_tarski(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_51])])).
% 0.20/0.50  cnf(c_0_88, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.50  cnf(c_0_89, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.50  cnf(c_0_90, negated_conjecture, (v1_funct_2(esk12_0,esk10_0,k2_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_49]), c_0_50]), c_0_51])])).
% 0.20/0.50  cnf(c_0_91, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~v1_xboole_0(k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.50  cnf(c_0_92, negated_conjecture, (v1_funct_2(esk12_0,esk10_0,X1)|~v5_relat_1(esk12_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_49]), c_0_50]), c_0_51])])).
% 0.20/0.50  cnf(c_0_93, negated_conjecture, (v5_relat_1(esk12_0,X1)|~v1_xboole_0(k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.50  cnf(c_0_94, plain, (r1_tarski(k2_relat_1(esk6_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_95, negated_conjecture, (~v1_funct_2(esk12_0,esk10_0,esk11_0)|~r1_tarski(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_49]), c_0_47])])).
% 0.20/0.50  cnf(c_0_96, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_88, c_0_69])).
% 0.20/0.50  cnf(c_0_97, negated_conjecture, (v1_partfun1(esk12_0,esk10_0)|v1_xboole_0(k2_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_60]), c_0_90]), c_0_50])])).
% 0.20/0.50  cnf(c_0_98, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk12_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.20/0.50  cnf(c_0_99, plain, (r1_tarski(k2_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_94])).
% 0.20/0.50  cnf(c_0_100, negated_conjecture, (~v1_partfun1(esk12_0,esk10_0)|~r1_tarski(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_50]), c_0_51]), c_0_49]), c_0_47])])).
% 0.20/0.50  cnf(c_0_101, negated_conjecture, (v1_partfun1(esk12_0,esk10_0)), inference(sr,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.50  cnf(c_0_102, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_99, c_0_31])).
% 0.20/0.50  cnf(c_0_103, negated_conjecture, (~r1_tarski(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])])).
% 0.20/0.50  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_42]), c_0_103]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 105
% 0.20/0.50  # Proof object clause steps            : 73
% 0.20/0.50  # Proof object formula steps           : 32
% 0.20/0.50  # Proof object conjectures             : 28
% 0.20/0.50  # Proof object clause conjectures      : 25
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 25
% 0.20/0.50  # Proof object initial formulas used   : 16
% 0.20/0.50  # Proof object generating inferences   : 33
% 0.20/0.50  # Proof object simplifying inferences  : 41
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 20
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 52
% 0.20/0.50  # Removed in clause preprocessing      : 5
% 0.20/0.50  # Initial clauses in saturation        : 47
% 0.20/0.50  # Processed clauses                    : 1876
% 0.20/0.50  # ...of these trivial                  : 4
% 0.20/0.50  # ...subsumed                          : 1260
% 0.20/0.50  # ...remaining for further processing  : 612
% 0.20/0.50  # Other redundant clauses eliminated   : 17
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 50
% 0.20/0.50  # Backward-rewritten                   : 13
% 0.20/0.50  # Generated clauses                    : 5099
% 0.20/0.50  # ...of the previous two non-trivial   : 4516
% 0.20/0.50  # Contextual simplify-reflections      : 36
% 0.20/0.50  # Paramodulations                      : 5083
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 17
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 487
% 0.20/0.50  #    Positive orientable unit clauses  : 30
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 13
% 0.20/0.50  #    Non-unit-clauses                  : 444
% 0.20/0.50  # Current number of unprocessed clauses: 2634
% 0.20/0.50  # ...number of literals in the above   : 11052
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 110
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 36738
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 20875
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 708
% 0.20/0.50  # Unit Clause-clause subsumption calls : 1483
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 11
% 0.20/0.50  # BW rewrite match successes           : 8
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 66863
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.155 s
% 0.20/0.50  # System time              : 0.010 s
% 0.20/0.50  # Total time               : 0.165 s
% 0.20/0.50  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
