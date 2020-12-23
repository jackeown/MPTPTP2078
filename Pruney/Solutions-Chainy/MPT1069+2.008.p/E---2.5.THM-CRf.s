%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:50 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 457 expanded)
%              Number of clauses        :   82 ( 186 expanded)
%              Number of leaves         :   20 ( 111 expanded)
%              Depth                    :   15
%              Number of atoms          :  416 (2483 expanded)
%              Number of equality atoms :   90 ( 506 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   2 average)
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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t8_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | k2_relset_1(X57,X58,X59) = k2_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    & v1_funct_1(esk9_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))
    & m1_subset_1(esk10_0,esk6_0)
    & r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))
    & esk6_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) != k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_25,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_26,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k1_relset_1(X54,X55,X56) = k1_relat_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_27,plain,(
    ! [X80,X81,X82,X83] :
      ( ( v1_funct_1(X83)
        | X81 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X80,X81,X83),X82)
        | ~ v1_funct_1(X83)
        | ~ v1_funct_2(X83,X80,X81)
        | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( v1_funct_2(X83,X80,X82)
        | X81 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X80,X81,X83),X82)
        | ~ v1_funct_1(X83)
        | ~ v1_funct_2(X83,X80,X81)
        | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X82)))
        | X81 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X80,X81,X83),X82)
        | ~ v1_funct_1(X83)
        | ~ v1_funct_2(X83,X80,X81)
        | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( v1_funct_1(X83)
        | X80 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X80,X81,X83),X82)
        | ~ v1_funct_1(X83)
        | ~ v1_funct_2(X83,X80,X81)
        | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( v1_funct_2(X83,X80,X82)
        | X80 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X80,X81,X83),X82)
        | ~ v1_funct_1(X83)
        | ~ v1_funct_2(X83,X80,X81)
        | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X82)))
        | X80 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X80,X81,X83),X82)
        | ~ v1_funct_1(X83)
        | ~ v1_funct_2(X83,X80,X81)
        | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

cnf(c_0_28,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk10_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(esk6_0,esk7_0,esk8_0) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_47,plain,(
    ! [X60,X61,X62] :
      ( ( v1_funct_1(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X60)
        | v1_xboole_0(X61) )
      & ( ~ v1_xboole_0(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X60)
        | v1_xboole_0(X61) )
      & ( v1_funct_2(X62,X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X60)
        | v1_xboole_0(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_48,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | v1_funct_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( k1_relset_1(esk7_0,esk5_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_55,plain,(
    ! [X76,X77,X78,X79] :
      ( ~ v1_funct_1(X79)
      | ~ v1_funct_2(X79,X76,X77)
      | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))
      | ~ r2_hidden(X78,X76)
      | X77 = k1_xboole_0
      | r2_hidden(k1_funct_1(X79,X78),X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_56,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_29])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_funct_2(esk8_0,esk6_0,X1)
    | ~ r1_tarski(k2_relat_1(esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_41]),c_0_42]),c_0_40])])).

fof(c_0_59,plain,(
    ! [X51,X52,X53] :
      ( ~ v1_xboole_0(X51)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | v1_xboole_0(X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_funct_2(esk8_0,esk6_0,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

fof(c_0_69,plain,(
    ! [X66,X67,X68,X69,X70,X71] :
      ( v1_xboole_0(X68)
      | ~ v1_funct_1(X69)
      | ~ v1_funct_2(X69,X67,X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | ~ v1_funct_1(X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X66)))
      | ~ m1_subset_1(X71,X67)
      | ~ r1_tarski(k2_relset_1(X67,X68,X69),k1_relset_1(X68,X66,X70))
      | X67 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X67,X68,X66,X69,X70),X71) = k1_funct_1(X70,k1_funct_1(X69,X71)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk2_2(esk8_0,X1),k2_zfmisc_1(esk6_0,esk7_0))
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_32])).

cnf(c_0_76,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_40])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_42])]),c_0_68])).

fof(c_0_79,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | v1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(k2_zfmisc_1(X3,X4))
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_29]),c_0_41])]),c_0_73]),c_0_74])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),k2_zfmisc_1(esk6_0,esk7_0))
    | v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_75])).

fof(c_0_86,plain,(
    ! [X22,X23] :
      ( ( k2_zfmisc_1(X22,X23) != k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_87,plain,(
    ! [X63,X64,X65] :
      ( ~ v1_relat_1(X64)
      | ~ v5_relat_1(X64,X63)
      | ~ v1_funct_1(X64)
      | ~ r2_hidden(X65,k1_relat_1(X64))
      | k7_partfun1(X63,X64,X65) = k1_funct_1(X64,X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,esk10_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_63])).

cnf(c_0_90,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_91,plain,(
    ! [X48,X49,X50] :
      ( ( v4_relat_1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v5_relat_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3) = k1_funct_1(esk9_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk7_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_38]),c_0_81]),c_0_54])]),c_0_73])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_29]),c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0))
    | v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_96,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,esk10_0),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_38])).

cnf(c_0_99,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_41]),c_0_42]),c_0_29]),c_0_40]),c_0_77])]),c_0_51])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_103,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_104,negated_conjecture,
    ( k7_partfun1(X1,esk9_0,k1_funct_1(esk8_0,esk10_0)) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))
    | k2_relat_1(esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | ~ v5_relat_1(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_81]),c_0_98])])).

cnf(c_0_105,negated_conjecture,
    ( v5_relat_1(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_38])).

cnf(c_0_106,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) != k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_35])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])])).

cnf(c_0_109,negated_conjecture,
    ( k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))
    | k2_relat_1(esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) != k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_108])).

cnf(c_0_113,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_114,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_115,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk1_1(esk8_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_83])).

cnf(c_0_117,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_102]),c_0_103])])).

cnf(c_0_118,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_114]),c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_83])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120]),c_0_115]),c_0_103])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.44/0.63  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.44/0.63  # and selection function SelectNewComplexAHP.
% 0.44/0.63  #
% 0.44/0.63  # Preprocessing time       : 0.049 s
% 0.44/0.63  # Presaturation interreduction done
% 0.44/0.63  
% 0.44/0.63  # Proof found!
% 0.44/0.63  # SZS status Theorem
% 0.44/0.63  # SZS output start CNFRefutation
% 0.44/0.63  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.44/0.63  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.44/0.63  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.44/0.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.44/0.63  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.44/0.63  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.44/0.63  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 0.44/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.44/0.63  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.44/0.63  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.44/0.63  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.44/0.63  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.44/0.63  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.44/0.63  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.44/0.63  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.44/0.63  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.44/0.63  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.44/0.63  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.44/0.63  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.44/0.63  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.44/0.63  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.44/0.63  fof(c_0_21, plain, ![X57, X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|k2_relset_1(X57,X58,X59)=k2_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.44/0.63  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk7_0)&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((v1_funct_1(esk9_0)&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))))&(m1_subset_1(esk10_0,esk6_0)&(r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))&(esk6_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)!=k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.44/0.63  fof(c_0_23, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.44/0.63  fof(c_0_24, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.44/0.63  fof(c_0_25, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.44/0.63  fof(c_0_26, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|k1_relset_1(X54,X55,X56)=k1_relat_1(X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.44/0.63  fof(c_0_27, plain, ![X80, X81, X82, X83]:((((v1_funct_1(X83)|X81=k1_xboole_0|~r1_tarski(k2_relset_1(X80,X81,X83),X82)|(~v1_funct_1(X83)|~v1_funct_2(X83,X80,X81)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81)))))&(v1_funct_2(X83,X80,X82)|X81=k1_xboole_0|~r1_tarski(k2_relset_1(X80,X81,X83),X82)|(~v1_funct_1(X83)|~v1_funct_2(X83,X80,X81)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))))&(m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X82)))|X81=k1_xboole_0|~r1_tarski(k2_relset_1(X80,X81,X83),X82)|(~v1_funct_1(X83)|~v1_funct_2(X83,X80,X81)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))))&(((v1_funct_1(X83)|X80!=k1_xboole_0|~r1_tarski(k2_relset_1(X80,X81,X83),X82)|(~v1_funct_1(X83)|~v1_funct_2(X83,X80,X81)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81)))))&(v1_funct_2(X83,X80,X82)|X80!=k1_xboole_0|~r1_tarski(k2_relset_1(X80,X81,X83),X82)|(~v1_funct_1(X83)|~v1_funct_2(X83,X80,X81)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))))&(m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X82)))|X80!=k1_xboole_0|~r1_tarski(k2_relset_1(X80,X81,X83),X82)|(~v1_funct_1(X83)|~v1_funct_2(X83,X80,X81)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.44/0.63  cnf(c_0_28, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.44/0.63  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  fof(c_0_30, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.44/0.63  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.44/0.63  cnf(c_0_32, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.44/0.63  fof(c_0_33, plain, ![X17]:(~v1_xboole_0(X17)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.44/0.63  cnf(c_0_34, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.44/0.63  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk10_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  fof(c_0_36, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|m1_subset_1(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.44/0.63  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.44/0.63  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.44/0.63  cnf(c_0_40, negated_conjecture, (k2_relset_1(esk6_0,esk7_0,esk8_0)=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.44/0.63  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.44/0.63  cnf(c_0_44, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.44/0.63  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.44/0.63  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.44/0.63  fof(c_0_47, plain, ![X60, X61, X62]:(((v1_funct_1(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61)))&(~v1_xboole_0(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61))))&(v1_funct_2(X62,X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.44/0.63  fof(c_0_48, plain, ![X40]:(~v1_xboole_0(X40)|v1_funct_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.44/0.63  cnf(c_0_49, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.44/0.63  cnf(c_0_50, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.44/0.63  cnf(c_0_51, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_52, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.44/0.63  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_54, negated_conjecture, (k1_relset_1(esk7_0,esk5_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.44/0.63  fof(c_0_55, plain, ![X76, X77, X78, X79]:(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))|(~r2_hidden(X78,X76)|(X77=k1_xboole_0|r2_hidden(k1_funct_1(X79,X78),X77)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.44/0.63  cnf(c_0_56, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))|~r1_tarski(k2_relat_1(esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_29])])).
% 0.44/0.63  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.44/0.63  cnf(c_0_58, negated_conjecture, (esk7_0=k1_xboole_0|v1_funct_2(esk8_0,esk6_0,X1)|~r1_tarski(k2_relat_1(esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_41]), c_0_42]), c_0_40])])).
% 0.44/0.63  fof(c_0_59, plain, ![X51, X52, X53]:(~v1_xboole_0(X51)|(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_xboole_0(X53))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.44/0.63  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.44/0.63  cnf(c_0_61, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.44/0.63  cnf(c_0_62, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.44/0.63  cnf(c_0_63, negated_conjecture, (r2_hidden(esk10_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.44/0.63  cnf(c_0_64, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_29])).
% 0.44/0.63  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relat_1(esk9_0))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.44/0.63  cnf(c_0_66, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.44/0.63  cnf(c_0_67, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0))))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.44/0.63  cnf(c_0_68, negated_conjecture, (esk7_0=k1_xboole_0|v1_funct_2(esk8_0,esk6_0,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 0.44/0.63  fof(c_0_69, plain, ![X66, X67, X68, X69, X70, X71]:(v1_xboole_0(X68)|(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|(~v1_funct_1(X70)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X66)))|(~m1_subset_1(X71,X67)|(~r1_tarski(k2_relset_1(X67,X68,X69),k1_relset_1(X68,X66,X70))|(X67=k1_xboole_0|k1_funct_1(k8_funct_2(X67,X68,X66,X69,X70),X71)=k1_funct_1(X70,k1_funct_1(X69,X71)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.44/0.63  cnf(c_0_70, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.44/0.63  cnf(c_0_71, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.44/0.63  cnf(c_0_72, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 0.44/0.63  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_63])).
% 0.44/0.63  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk2_2(esk8_0,X1),k2_zfmisc_1(esk6_0,esk7_0))|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_32])).
% 0.44/0.63  cnf(c_0_76, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.44/0.63  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(rw,[status(thm)],[c_0_65, c_0_40])).
% 0.44/0.63  cnf(c_0_78, negated_conjecture, (k2_relat_1(esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_42])]), c_0_68])).
% 0.44/0.63  fof(c_0_79, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|v1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.44/0.63  cnf(c_0_80, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.44/0.63  cnf(c_0_81, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_82, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(k2_zfmisc_1(X3,X4))|~v1_xboole_0(X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.44/0.63  cnf(c_0_83, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_29]), c_0_41])]), c_0_73]), c_0_74])).
% 0.44/0.63  cnf(c_0_84, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.44/0.63  cnf(c_0_85, negated_conjecture, (r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),k2_zfmisc_1(esk6_0,esk7_0))|v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_75])).
% 0.44/0.63  fof(c_0_86, plain, ![X22, X23]:((k2_zfmisc_1(X22,X23)!=k1_xboole_0|(X22=k1_xboole_0|X23=k1_xboole_0))&((X22!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0)&(X23!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.44/0.63  fof(c_0_87, plain, ![X63, X64, X65]:(~v1_relat_1(X64)|~v5_relat_1(X64,X63)|~v1_funct_1(X64)|(~r2_hidden(X65,k1_relat_1(X64))|k7_partfun1(X63,X64,X65)=k1_funct_1(X64,X65))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.44/0.63  cnf(c_0_88, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk9_0))|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.44/0.63  cnf(c_0_89, negated_conjecture, (k2_relat_1(esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,esk10_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_63])).
% 0.44/0.63  cnf(c_0_90, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.44/0.63  fof(c_0_91, plain, ![X48, X49, X50]:((v4_relat_1(X50,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v5_relat_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.44/0.63  cnf(c_0_92, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3)=k1_funct_1(esk9_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk7_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_38]), c_0_81]), c_0_54])]), c_0_73])).
% 0.44/0.63  cnf(c_0_93, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))|~v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_29]), c_0_83])).
% 0.44/0.63  cnf(c_0_94, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0))|v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.44/0.63  cnf(c_0_95, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.44/0.63  cnf(c_0_96, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.44/0.63  cnf(c_0_97, negated_conjecture, (k2_relat_1(esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,esk10_0),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.44/0.63  cnf(c_0_98, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_90, c_0_38])).
% 0.44/0.63  cnf(c_0_99, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.44/0.63  cnf(c_0_100, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_41]), c_0_42]), c_0_29]), c_0_40]), c_0_77])]), c_0_51])).
% 0.44/0.63  cnf(c_0_101, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0))|~v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.44/0.63  cnf(c_0_102, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_95])).
% 0.44/0.63  cnf(c_0_103, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.44/0.63  cnf(c_0_104, negated_conjecture, (k7_partfun1(X1,esk9_0,k1_funct_1(esk8_0,esk10_0))=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))|k2_relat_1(esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|~v5_relat_1(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_81]), c_0_98])])).
% 0.44/0.63  cnf(c_0_105, negated_conjecture, (v5_relat_1(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_99, c_0_38])).
% 0.44/0.63  cnf(c_0_106, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)!=k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.63  cnf(c_0_107, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(spm,[status(thm)],[c_0_100, c_0_35])).
% 0.44/0.63  cnf(c_0_108, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])])).
% 0.44/0.63  cnf(c_0_109, negated_conjecture, (k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))|k2_relat_1(esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.44/0.63  cnf(c_0_110, negated_conjecture, (k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))!=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 0.44/0.63  cnf(c_0_111, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.44/0.63  cnf(c_0_112, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_76, c_0_108])).
% 0.44/0.63  cnf(c_0_113, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.44/0.63  cnf(c_0_114, negated_conjecture, (k2_relat_1(esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_109, c_0_110])).
% 0.44/0.63  cnf(c_0_115, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_111])).
% 0.44/0.63  cnf(c_0_116, negated_conjecture, (r2_hidden(esk1_1(esk8_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_83])).
% 0.44/0.63  cnf(c_0_117, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_102]), c_0_103])])).
% 0.44/0.63  cnf(c_0_118, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_114]), c_0_115])).
% 0.44/0.63  cnf(c_0_119, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_116])).
% 0.44/0.63  cnf(c_0_120, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_83])).
% 0.44/0.63  cnf(c_0_121, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120]), c_0_115]), c_0_103])]), ['proof']).
% 0.44/0.63  # SZS output end CNFRefutation
% 0.44/0.63  # Proof object total steps             : 122
% 0.44/0.63  # Proof object clause steps            : 82
% 0.44/0.63  # Proof object formula steps           : 40
% 0.44/0.63  # Proof object conjectures             : 51
% 0.44/0.63  # Proof object clause conjectures      : 48
% 0.44/0.63  # Proof object formula conjectures     : 3
% 0.44/0.63  # Proof object initial clauses used    : 35
% 0.44/0.63  # Proof object initial formulas used   : 20
% 0.44/0.63  # Proof object generating inferences   : 40
% 0.44/0.63  # Proof object simplifying inferences  : 47
% 0.44/0.63  # Training examples: 0 positive, 0 negative
% 0.44/0.63  # Parsed axioms                        : 30
% 0.44/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.44/0.63  # Initial clauses                      : 61
% 0.44/0.63  # Removed in clause preprocessing      : 6
% 0.44/0.63  # Initial clauses in saturation        : 55
% 0.44/0.63  # Processed clauses                    : 2406
% 0.44/0.63  # ...of these trivial                  : 4
% 0.44/0.63  # ...subsumed                          : 1375
% 0.44/0.63  # ...remaining for further processing  : 1027
% 0.44/0.63  # Other redundant clauses eliminated   : 10
% 0.44/0.63  # Clauses deleted for lack of memory   : 0
% 0.44/0.63  # Backward-subsumed                    : 168
% 0.44/0.63  # Backward-rewritten                   : 620
% 0.44/0.63  # Generated clauses                    : 6203
% 0.44/0.63  # ...of the previous two non-trivial   : 5998
% 0.44/0.63  # Contextual simplify-reflections      : 21
% 0.44/0.63  # Paramodulations                      : 6174
% 0.44/0.63  # Factorizations                       : 4
% 0.44/0.63  # Equation resolutions                 : 20
% 0.44/0.63  # Propositional unsat checks           : 0
% 0.44/0.63  #    Propositional check models        : 0
% 0.44/0.63  #    Propositional check unsatisfiable : 0
% 0.44/0.63  #    Propositional clauses             : 0
% 0.44/0.63  #    Propositional clauses after purity: 0
% 0.44/0.63  #    Propositional unsat core size     : 0
% 0.44/0.63  #    Propositional preprocessing time  : 0.000
% 0.44/0.63  #    Propositional encoding time       : 0.000
% 0.44/0.63  #    Propositional solver time         : 0.000
% 0.44/0.63  #    Success case prop preproc time    : 0.000
% 0.44/0.63  #    Success case prop encoding time   : 0.000
% 0.44/0.63  #    Success case prop solver time     : 0.000
% 0.44/0.63  # Current number of processed clauses  : 178
% 0.44/0.63  #    Positive orientable unit clauses  : 28
% 0.44/0.63  #    Positive unorientable unit clauses: 0
% 0.44/0.63  #    Negative unit clauses             : 10
% 0.44/0.63  #    Non-unit-clauses                  : 140
% 0.44/0.63  # Current number of unprocessed clauses: 3489
% 0.44/0.63  # ...number of literals in the above   : 19946
% 0.44/0.63  # Current number of archived formulas  : 0
% 0.44/0.63  # Current number of archived clauses   : 847
% 0.44/0.63  # Clause-clause subsumption calls (NU) : 168952
% 0.44/0.63  # Rec. Clause-clause subsumption calls : 42461
% 0.44/0.63  # Non-unit clause-clause subsumptions  : 1490
% 0.44/0.63  # Unit Clause-clause subsumption calls : 1282
% 0.44/0.63  # Rewrite failures with RHS unbound    : 0
% 0.44/0.63  # BW rewrite match attempts            : 20
% 0.44/0.63  # BW rewrite match successes           : 11
% 0.44/0.63  # Condensation attempts                : 0
% 0.44/0.63  # Condensation successes               : 0
% 0.44/0.63  # Termbank termtop insertions          : 104628
% 0.44/0.63  
% 0.44/0.63  # -------------------------------------------------
% 0.44/0.63  # User time                : 0.273 s
% 0.44/0.63  # System time              : 0.011 s
% 0.44/0.63  # Total time               : 0.284 s
% 0.44/0.63  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
