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
% DateTime   : Thu Dec  3 11:07:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 262 expanded)
%              Number of clauses        :   45 ( 105 expanded)
%              Number of leaves         :   15 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  289 (1478 expanded)
%              Number of equality atoms :   63 ( 322 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t155_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t111_relat_1,axiom,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_partfun1(X3,X4)
             => ( ( X2 = k1_xboole_0
                  & X1 != k1_xboole_0 )
                | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t155_funct_2])).

fof(c_0_16,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | v1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk14_0)
    & m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))
    & v1_funct_1(esk15_0)
    & v1_funct_2(esk15_0,esk12_0,esk13_0)
    & m1_subset_1(esk15_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))
    & r1_partfun1(esk14_0,esk15_0)
    & ( esk13_0 != k1_xboole_0
      | esk12_0 = k1_xboole_0 )
    & ~ r2_hidden(esk15_0,k5_partfun1(esk12_0,esk13_0,esk14_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X36] :
      ( ~ v1_relat_1(X36)
      | k7_relat_1(X36,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk15_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | v1_relat_1(k7_relat_1(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk15_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X74,X75,X76,X77,X78,X80,X81,X82,X84] :
      ( ( v1_funct_1(esk9_5(X74,X75,X76,X77,X78))
        | ~ r2_hidden(X78,X77)
        | X77 != k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( m1_subset_1(esk9_5(X74,X75,X76,X77,X78),k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | ~ r2_hidden(X78,X77)
        | X77 != k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( esk9_5(X74,X75,X76,X77,X78) = X78
        | ~ r2_hidden(X78,X77)
        | X77 != k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( v1_partfun1(esk9_5(X74,X75,X76,X77,X78),X74)
        | ~ r2_hidden(X78,X77)
        | X77 != k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( r1_partfun1(X76,esk9_5(X74,X75,X76,X77,X78))
        | ~ r2_hidden(X78,X77)
        | X77 != k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( ~ v1_funct_1(X81)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | X81 != X80
        | ~ v1_partfun1(X81,X74)
        | ~ r1_partfun1(X76,X81)
        | r2_hidden(X80,X77)
        | X77 != k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( ~ r2_hidden(esk10_4(X74,X75,X76,X82),X82)
        | ~ v1_funct_1(X84)
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | X84 != esk10_4(X74,X75,X76,X82)
        | ~ v1_partfun1(X84,X74)
        | ~ r1_partfun1(X76,X84)
        | X82 = k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( v1_funct_1(esk11_4(X74,X75,X76,X82))
        | r2_hidden(esk10_4(X74,X75,X76,X82),X82)
        | X82 = k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( m1_subset_1(esk11_4(X74,X75,X76,X82),k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | r2_hidden(esk10_4(X74,X75,X76,X82),X82)
        | X82 = k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( esk11_4(X74,X75,X76,X82) = esk10_4(X74,X75,X76,X82)
        | r2_hidden(esk10_4(X74,X75,X76,X82),X82)
        | X82 = k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( v1_partfun1(esk11_4(X74,X75,X76,X82),X74)
        | r2_hidden(esk10_4(X74,X75,X76,X82),X82)
        | X82 = k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( r1_partfun1(X76,esk11_4(X74,X75,X76,X82))
        | r2_hidden(esk10_4(X74,X75,X76,X82),X82)
        | X82 = k5_partfun1(X74,X75,X76)
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_25,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k1_relat_1(k7_relat_1(X39,X38)) = k3_xboole_0(k1_relat_1(X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_26,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k7_relat_1(esk15_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X37] : k7_relat_1(k1_xboole_0,X37) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t111_relat_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X20,X21] :
      ( ( ~ r1_xboole_0(X20,X21)
        | k3_xboole_0(X20,X21) = k1_xboole_0 )
      & ( k3_xboole_0(X20,X21) != k1_xboole_0
        | r1_xboole_0(X20,X21) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_31,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])])).

cnf(c_0_33,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_35,plain,(
    ! [X68,X69,X70] :
      ( ( v1_funct_1(X70)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | v1_xboole_0(X69) )
      & ( v1_partfun1(X70,X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | v1_xboole_0(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_39,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r2_hidden(esk3_2(X22,X23),X22)
        | r1_xboole_0(X22,X23) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r1_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_42,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk15_0,esk12_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk12_0,esk13_0,esk14_0))
    | ~ r1_partfun1(esk14_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,esk12_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( r1_partfun1(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk15_0,k5_partfun1(esk12_0,esk13_0,esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X65,X66,X67] :
      ( ~ v1_xboole_0(X65)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | v1_partfun1(X67,X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

fof(c_0_53,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | X28 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_54,negated_conjecture,
    ( v1_partfun1(esk15_0,esk12_0)
    | v1_xboole_0(esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_20]),c_0_43]),c_0_44])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_partfun1(esk15_0,esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_44]),c_0_20])]),c_0_47])).

fof(c_0_56,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk13_0) ),
    inference(sr,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(esk3_2(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( v1_partfun1(esk15_0,esk12_0)
    | ~ v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_20])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk13_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( esk13_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( v1_partfun1(esk15_0,esk12_0)
    | r2_hidden(esk1_1(esk12_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk12_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_57])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_71,c_0_55]),c_0_72]),c_0_72]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.13/0.40  # and selection function SelectNewComplexAHP.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.030 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t155_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 0.13/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.40  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 0.13/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.40  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.13/0.40  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.13/0.40  fof(t111_relat_1, axiom, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 0.13/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.40  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.13/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.40  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.13/0.40  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 0.13/0.40  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t155_funct_2])).
% 0.13/0.40  fof(c_0_16, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.40  fof(c_0_17, negated_conjecture, ((v1_funct_1(esk14_0)&m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))))&(((v1_funct_1(esk15_0)&v1_funct_2(esk15_0,esk12_0,esk13_0))&m1_subset_1(esk15_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))))&(r1_partfun1(esk14_0,esk15_0)&((esk13_0!=k1_xboole_0|esk12_0=k1_xboole_0)&~r2_hidden(esk15_0,k5_partfun1(esk12_0,esk13_0,esk14_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.40  fof(c_0_18, plain, ![X36]:(~v1_relat_1(X36)|k7_relat_1(X36,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.13/0.40  cnf(c_0_19, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk15_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_21, plain, ![X34, X35]:(~v1_relat_1(X34)|v1_relat_1(k7_relat_1(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.40  cnf(c_0_22, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk15_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.40  fof(c_0_24, plain, ![X74, X75, X76, X77, X78, X80, X81, X82, X84]:(((((((v1_funct_1(esk9_5(X74,X75,X76,X77,X78))|~r2_hidden(X78,X77)|X77!=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))))&(m1_subset_1(esk9_5(X74,X75,X76,X77,X78),k1_zfmisc_1(k2_zfmisc_1(X74,X75)))|~r2_hidden(X78,X77)|X77!=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(esk9_5(X74,X75,X76,X77,X78)=X78|~r2_hidden(X78,X77)|X77!=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(v1_partfun1(esk9_5(X74,X75,X76,X77,X78),X74)|~r2_hidden(X78,X77)|X77!=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(r1_partfun1(X76,esk9_5(X74,X75,X76,X77,X78))|~r2_hidden(X78,X77)|X77!=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(~v1_funct_1(X81)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))|X81!=X80|~v1_partfun1(X81,X74)|~r1_partfun1(X76,X81)|r2_hidden(X80,X77)|X77!=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&((~r2_hidden(esk10_4(X74,X75,X76,X82),X82)|(~v1_funct_1(X84)|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))|X84!=esk10_4(X74,X75,X76,X82)|~v1_partfun1(X84,X74)|~r1_partfun1(X76,X84))|X82=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))))&(((((v1_funct_1(esk11_4(X74,X75,X76,X82))|r2_hidden(esk10_4(X74,X75,X76,X82),X82)|X82=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))))&(m1_subset_1(esk11_4(X74,X75,X76,X82),k1_zfmisc_1(k2_zfmisc_1(X74,X75)))|r2_hidden(esk10_4(X74,X75,X76,X82),X82)|X82=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(esk11_4(X74,X75,X76,X82)=esk10_4(X74,X75,X76,X82)|r2_hidden(esk10_4(X74,X75,X76,X82),X82)|X82=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(v1_partfun1(esk11_4(X74,X75,X76,X82),X74)|r2_hidden(esk10_4(X74,X75,X76,X82),X82)|X82=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(r1_partfun1(X76,esk11_4(X74,X75,X76,X82))|r2_hidden(esk10_4(X74,X75,X76,X82),X82)|X82=k5_partfun1(X74,X75,X76)|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.13/0.40  fof(c_0_25, plain, ![X38, X39]:(~v1_relat_1(X39)|k1_relat_1(k7_relat_1(X39,X38))=k3_xboole_0(k1_relat_1(X39),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.13/0.40  cnf(c_0_26, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (k7_relat_1(esk15_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  fof(c_0_28, plain, ![X37]:k7_relat_1(k1_xboole_0,X37)=k1_xboole_0, inference(variable_rename,[status(thm)],[t111_relat_1])).
% 0.13/0.40  cnf(c_0_29, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  fof(c_0_30, plain, ![X20, X21]:((~r1_xboole_0(X20,X21)|k3_xboole_0(X20,X21)=k1_xboole_0)&(k3_xboole_0(X20,X21)!=k1_xboole_0|r1_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.40  cnf(c_0_31, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])])).
% 0.13/0.40  cnf(c_0_33, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.40  fof(c_0_35, plain, ![X68, X69, X70]:((v1_funct_1(X70)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69))|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|v1_xboole_0(X69))&(v1_partfun1(X70,X68)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69))|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|v1_xboole_0(X69))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.13/0.40  cnf(c_0_36, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_39, plain, ![X22, X23, X25, X26, X27]:(((r2_hidden(esk3_2(X22,X23),X22)|r1_xboole_0(X22,X23))&(r2_hidden(esk3_2(X22,X23),X23)|r1_xboole_0(X22,X23)))&(~r2_hidden(X27,X25)|~r2_hidden(X27,X26)|~r1_xboole_0(X25,X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.40  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.40  cnf(c_0_42, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk15_0,esk12_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk15_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk12_0,esk13_0,esk14_0))|~r1_partfun1(esk14_0,X1)|~v1_funct_1(X1)|~v1_partfun1(X1,esk12_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (r1_partfun1(esk14_0,esk15_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk15_0,k5_partfun1(esk12_0,esk13_0,esk14_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_51, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  fof(c_0_52, plain, ![X65, X66, X67]:(~v1_xboole_0(X65)|(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|v1_partfun1(X67,X65))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.20/0.40  fof(c_0_53, plain, ![X28]:(~v1_xboole_0(X28)|X28=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (v1_partfun1(esk15_0,esk12_0)|v1_xboole_0(esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_20]), c_0_43]), c_0_44])])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (~v1_partfun1(esk15_0,esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_44]), c_0_20])]), c_0_47])).
% 0.20/0.40  fof(c_0_56, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.40  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_59, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  fof(c_0_60, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_61, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (v1_xboole_0(esk13_0)), inference(sr,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.40  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0|~r2_hidden(esk3_2(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (v1_partfun1(esk15_0,esk12_0)|~v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_59, c_0_20])).
% 0.20/0.40  cnf(c_0_66, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (esk12_0=k1_xboole_0|esk13_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (esk13_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.40  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_63])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (v1_partfun1(esk15_0,esk12_0)|r2_hidden(esk1_1(esk12_0),esk12_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (esk12_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_57])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_71, c_0_55]), c_0_72]), c_0_72]), c_0_73]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 75
% 0.20/0.40  # Proof object clause steps            : 45
% 0.20/0.40  # Proof object formula steps           : 30
% 0.20/0.40  # Proof object conjectures             : 29
% 0.20/0.40  # Proof object clause conjectures      : 26
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 24
% 0.20/0.40  # Proof object initial formulas used   : 15
% 0.20/0.40  # Proof object generating inferences   : 16
% 0.20/0.40  # Proof object simplifying inferences  : 25
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 23
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 62
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 61
% 0.20/0.40  # Processed clauses                    : 325
% 0.20/0.40  # ...of these trivial                  : 2
% 0.20/0.40  # ...subsumed                          : 76
% 0.20/0.40  # ...remaining for further processing  : 246
% 0.20/0.40  # Other redundant clauses eliminated   : 16
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 88
% 0.20/0.40  # Generated clauses                    : 520
% 0.20/0.40  # ...of the previous two non-trivial   : 544
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 500
% 0.20/0.40  # Factorizations                       : 4
% 0.20/0.40  # Equation resolutions                 : 16
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 82
% 0.20/0.40  #    Positive orientable unit clauses  : 13
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 68
% 0.20/0.40  # Current number of unprocessed clauses: 340
% 0.20/0.40  # ...number of literals in the above   : 897
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 150
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 4930
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 2351
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 74
% 0.20/0.40  # Unit Clause-clause subsumption calls : 258
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 9
% 0.20/0.40  # BW rewrite match successes           : 7
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 12062
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.048 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.054 s
% 0.20/0.40  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
