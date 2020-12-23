%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t146_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:31 EDT 2019

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   73 (4898 expanded)
%              Number of clauses        :   54 (1650 expanded)
%              Number of leaves         :   10 (1160 expanded)
%              Depth                    :   18
%              Number of atoms          :  267 (40133 expanded)
%              Number of equality atoms :   63 (6953 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( r2_hidden(X4,k1_relset_1(X1,X1,X2))
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',t146_funct_2)).

fof(t145_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
           => ( r1_partfun1(X3,X4)
            <=> ! [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',t145_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',existence_m1_subset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',dt_k1_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',t8_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',t5_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t146_funct_2.p',d2_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X1,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_2])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( ~ r1_partfun1(X27,X28)
        | ~ r2_hidden(X29,k1_relset_1(X25,X26,X27))
        | k1_funct_1(X27,X29) = k1_funct_1(X28,X29)
        | X26 = k1_xboole_0
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(esk6_4(X25,X26,X27,X28),k1_relset_1(X25,X26,X27))
        | r1_partfun1(X27,X28)
        | X26 = k1_xboole_0
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( k1_funct_1(X27,esk6_4(X25,X26,X27,X28)) != k1_funct_1(X28,esk6_4(X25,X26,X27,X28))
        | r1_partfun1(X27,X28)
        | X26 = k1_xboole_0
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ r1_partfun1(X27,X28)
        | ~ r2_hidden(X29,k1_relset_1(X25,X26,X27))
        | k1_funct_1(X27,X29) = k1_funct_1(X28,X29)
        | X25 != k1_xboole_0
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(esk6_4(X25,X26,X27,X28),k1_relset_1(X25,X26,X27))
        | r1_partfun1(X27,X28)
        | X25 != k1_xboole_0
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( k1_funct_1(X27,esk6_4(X25,X26,X27,X28)) != k1_funct_1(X28,esk6_4(X25,X26,X27,X28))
        | r1_partfun1(X27,X28)
        | X25 != k1_xboole_0
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_2])])])])])).

fof(c_0_12,negated_conjecture,(
    ! [X10] :
      ( v1_funct_1(esk2_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk1_0,esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
      & ( r2_hidden(esk4_0,k1_relset_1(esk1_0,esk1_0,esk2_0))
        | ~ r1_partfun1(esk2_0,esk3_0) )
      & ( k1_funct_1(esk2_0,esk4_0) != k1_funct_1(esk3_0,esk4_0)
        | ~ r1_partfun1(esk2_0,esk3_0) )
      & ( r1_partfun1(esk2_0,esk3_0)
        | ~ r2_hidden(X10,k1_relset_1(esk1_0,esk1_0,esk2_0))
        | k1_funct_1(esk2_0,X10) = k1_funct_1(esk3_0,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relset_1(X1,X2,X3))
    | r1_partfun1(X3,X4)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
    | X5 = k1_xboole_0
    | ~ r1_partfun1(X1,X2)
    | ~ r2_hidden(X3,k1_relset_1(X4,X5,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_xboole_0 = esk1_0
    | r2_hidden(esk6_4(esk1_0,esk1_0,X1,esk3_0),k1_relset_1(esk1_0,esk1_0,X1))
    | r1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(X1,X2) = k1_funct_1(esk3_0,X2)
    | k1_xboole_0 = esk1_0
    | ~ r2_hidden(X2,k1_relset_1(esk1_0,esk1_0,X1))
    | ~ r1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( r1_partfun1(esk2_0,esk3_0)
    | k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relset_1(esk1_0,esk1_0,esk2_0))
    | ~ r1_partfun1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( k1_xboole_0 = esk1_0
    | r2_hidden(esk6_4(esk1_0,esk1_0,esk2_0,esk3_0),k1_relset_1(esk1_0,esk1_0,esk2_0))
    | r1_partfun1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk2_0,X1)
    | k1_xboole_0 = esk1_0
    | ~ r2_hidden(X1,k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_20])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k1_xboole_0 = esk1_0
    | r2_hidden(esk6_4(esk1_0,esk1_0,esk2_0,esk3_0),k1_relset_1(esk1_0,esk1_0,esk2_0))
    | r2_hidden(esk4_0,k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_4(esk1_0,esk1_0,esk2_0,esk3_0)) = k1_funct_1(esk2_0,esk6_4(esk1_0,esk1_0,esk2_0,esk3_0))
    | k1_xboole_0 = esk1_0
    | r2_hidden(esk4_0,k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_28,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,plain,(
    ! [X16] : m1_subset_1(esk5_1(X16),X16) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_30,plain,
    ( r1_partfun1(X1,X4)
    | X3 = k1_xboole_0
    | k1_funct_1(X1,esk6_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk6_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_4(esk1_0,esk1_0,esk2_0,esk3_0)) = k1_funct_1(esk2_0,esk6_4(esk1_0,esk1_0,esk2_0,esk3_0))
    | k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk2_0,esk4_0)
    | k1_xboole_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_27])).

fof(c_0_32,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k1_relset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_33,plain,(
    ! [X46,X47] :
      ( ~ v1_xboole_0(X46)
      | X46 = X47
      | ~ v1_xboole_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_37,plain,(
    ! [X43] :
      ( ~ v1_xboole_0(X43)
      | X43 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk2_0,esk4_0)
    | k1_xboole_0 = esk1_0
    | r1_partfun1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_14]),c_0_15]),c_0_19]),c_0_16]),c_0_20])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) != k1_funct_1(esk3_0,esk4_0)
    | ~ r1_partfun1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk2_0,esk4_0)
    | k1_xboole_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_38]),c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_relset_1(esk1_0,esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_47,plain,
    ( X1 = X2
    | r2_hidden(esk5_1(X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_50,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_51,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_52,negated_conjecture,
    ( k1_xboole_0 = esk1_0
    | ~ r1_partfun1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_46])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_hidden(esk5_1(X1),X1)
    | r2_hidden(esk5_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_55,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( k1_xboole_0 = esk1_0
    | r2_hidden(esk6_4(esk1_0,esk1_0,esk2_0,esk3_0),k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( X1 = k1_relset_1(esk1_0,esk1_0,esk2_0)
    | r2_hidden(esk5_1(X1),X1)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( esk5_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_4(esk1_0,esk1_0,esk2_0,esk3_0)) = k1_funct_1(esk2_0,esk6_4(esk1_0,esk1_0,esk2_0,esk3_0))
    | k1_xboole_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_57]),c_0_52])).

cnf(c_0_61,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relset_1(X1,X2,X3))
    | r1_partfun1(X3,X4)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k1_relset_1(esk1_0,esk1_0,esk2_0)
    | r2_hidden(esk5_1(esk1_0),esk1_0)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_41])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_59]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( k1_xboole_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_60]),c_0_14]),c_0_15]),c_0_19]),c_0_16]),c_0_20])]),c_0_52])).

cnf(c_0_65,plain,
    ( r2_hidden(esk6_4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
    | r1_partfun1(X2,X3)
    | ~ v1_funct_2(X3,k1_xboole_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    | r2_hidden(esk5_1(esk1_0),esk1_0) ),
    inference(ef,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
    ( r2_hidden(esk6_4(esk1_0,X1,X2,X3),k1_relset_1(esk1_0,X1,X2))
    | r1_partfun1(X2,X3)
    | ~ v1_funct_2(X3,esk1_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_64]),c_0_64]),c_0_64]),c_0_64]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(sr,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk6_4(esk1_0,esk1_0,X1,esk3_0),k1_relset_1(esk1_0,esk1_0,X1))
    | r1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_partfun1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_69]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_19]),c_0_69]),c_0_20])]),c_0_67]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
