%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:11 EST 2020

% Result     : Theorem 34.16s
% Output     : CNFRefutation 34.16s
% Verified   : 
% Statistics : Number of formulae       :   97 (15392 expanded)
%              Number of clauses        :   72 (7122 expanded)
%              Number of leaves         :   12 (4101 expanded)
%              Depth                    :   19
%              Number of atoms          :  281 (28881 expanded)
%              Number of equality atoms :   76 (4791 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t191_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ~ v1_xboole_0(X3)
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
             => ( ! [X5] :
                    ( m1_subset_1(X5,X2)
                   => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
               => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_14,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k2_relset_1(X23,X24,X25) = k2_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(k2_relset_1(X17,X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_18,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ~ v1_xboole_0(X3)
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
               => ( ! [X5] :
                      ( m1_subset_1(X5,X2)
                     => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
                 => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t191_funct_2])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(X35)
        | r2_hidden(esk1_3(X33,X34,X35),X33)
        | k1_relat_1(X35) != X33
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( v1_funct_2(X35,X33,X34)
        | r2_hidden(esk1_3(X33,X34,X35),X33)
        | k1_relat_1(X35) != X33
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | r2_hidden(esk1_3(X33,X34,X35),X33)
        | k1_relat_1(X35) != X33
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( v1_funct_1(X35)
        | ~ r2_hidden(k1_funct_1(X35,esk1_3(X33,X34,X35)),X34)
        | k1_relat_1(X35) != X33
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( v1_funct_2(X35,X33,X34)
        | ~ r2_hidden(k1_funct_1(X35,esk1_3(X33,X34,X35)),X34)
        | k1_relat_1(X35) != X33
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ r2_hidden(k1_funct_1(X35,esk1_3(X33,X34,X35)),X34)
        | k1_relat_1(X35) != X33
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_26,negated_conjecture,(
    ! [X41] :
      ( ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X41,esk3_0)
        | r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X41),esk2_0) )
      & ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_28,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(k1_xboole_0)) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_29,plain,
    ( k2_relset_1(X1,X2,k2_relset_1(X3,k2_zfmisc_1(X1,X2),X4)) = k2_relat_1(k2_relset_1(X3,k2_zfmisc_1(X1,X2),X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X28 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != k1_xboole_0
        | v1_funct_2(X28,X26,X27)
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_34,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_28]),c_0_23])])).

cnf(c_0_37,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k1_xboole_0))) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_28]),c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) = k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_37]),c_0_36])])).

fof(c_0_48,plain,(
    ! [X29,X30,X31,X32] :
      ( v1_xboole_0(X29)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X29,X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X32,X29)
      | k3_funct_2(X29,X30,X31,X32) = k1_funct_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_49,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | m1_subset_1(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1)))
    | r2_hidden(esk1_3(k1_relat_1(esk5_0),X1,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_32])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_16])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_relset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_46]),c_0_47])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | r2_hidden(esk1_3(esk3_0,X1,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_40]),c_0_32])]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k2_relset_1(X1,X2,k2_relset_1(X3,k2_zfmisc_1(X1,X2),k2_relset_1(X4,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)),X5))) = k2_relat_1(k2_relset_1(X3,k2_zfmisc_1(X1,X2),k2_relset_1(X4,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)),X5)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_64,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))) = k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_46]),c_0_46])).

cnf(c_0_65,plain,
    ( m1_subset_1(k2_relset_1(X1,k1_xboole_0,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_71,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))) = k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_47]),c_0_46]),c_0_64]),c_0_46]),c_0_64])).

cnf(c_0_72,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_64])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(k1_relat_1(X1),X2,X1)),X2) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))
    | k2_relset_1(esk3_0,X1,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_68]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_70])).

cnf(c_0_78,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))) = k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_54]),c_0_64]),c_0_71]),c_0_64]),c_0_71])).

cnf(c_0_79,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_71]),c_0_72])])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_40]),c_0_39])])).

cnf(c_0_81,negated_conjecture,
    ( k2_relset_1(esk3_0,X1,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_78]),c_0_79])])).

cnf(c_0_84,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_44])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_84]),c_0_69])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))
    | esk4_0 = k1_xboole_0
    | r1_tarski(k2_relset_1(esk3_0,X1,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_78])).

cnf(c_0_92,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk2_0,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,esk2_0,esk5_0))
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_87]),c_0_76])).

cnf(c_0_93,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_90]),c_0_76])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_relset_1(X1,X2,k2_relset_1(X3,X4,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_71])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_92]),c_0_80]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 34.16/34.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 34.16/34.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 34.16/34.38  #
% 34.16/34.38  # Preprocessing time       : 0.028 s
% 34.16/34.38  # Presaturation interreduction done
% 34.16/34.38  
% 34.16/34.38  # Proof found!
% 34.16/34.38  # SZS status Theorem
% 34.16/34.38  # SZS output start CNFRefutation
% 34.16/34.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 34.16/34.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 34.16/34.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 34.16/34.38  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 34.16/34.38  fof(t191_funct_2, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 34.16/34.38  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 34.16/34.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 34.16/34.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 34.16/34.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 34.16/34.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 34.16/34.38  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 34.16/34.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 34.16/34.38  fof(c_0_12, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 34.16/34.38  fof(c_0_13, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 34.16/34.38  fof(c_0_14, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k2_relset_1(X23,X24,X25)=k2_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 34.16/34.38  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 34.16/34.38  cnf(c_0_16, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 34.16/34.38  fof(c_0_17, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|m1_subset_1(k2_relset_1(X17,X18,X19),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 34.16/34.38  cnf(c_0_18, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 34.16/34.38  cnf(c_0_19, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 34.16/34.38  cnf(c_0_20, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 34.16/34.38  cnf(c_0_21, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 34.16/34.38  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1)))))), inference(assume_negation,[status(cth)],[t191_funct_2])).
% 34.16/34.38  cnf(c_0_23, plain, (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])])).
% 34.16/34.38  fof(c_0_24, plain, ![X33, X34, X35]:((((v1_funct_1(X35)|(r2_hidden(esk1_3(X33,X34,X35),X33)|k1_relat_1(X35)!=X33)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(v1_funct_2(X35,X33,X34)|(r2_hidden(esk1_3(X33,X34,X35),X33)|k1_relat_1(X35)!=X33)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|(r2_hidden(esk1_3(X33,X34,X35),X33)|k1_relat_1(X35)!=X33)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(((v1_funct_1(X35)|(~r2_hidden(k1_funct_1(X35,esk1_3(X33,X34,X35)),X34)|k1_relat_1(X35)!=X33)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(v1_funct_2(X35,X33,X34)|(~r2_hidden(k1_funct_1(X35,esk1_3(X33,X34,X35)),X34)|k1_relat_1(X35)!=X33)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|(~r2_hidden(k1_funct_1(X35,esk1_3(X33,X34,X35)),X34)|k1_relat_1(X35)!=X33)|(~v1_relat_1(X35)|~v1_funct_1(X35))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 34.16/34.38  fof(c_0_25, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 34.16/34.38  fof(c_0_26, negated_conjecture, ![X41]:(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((~m1_subset_1(X41,esk3_0)|r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X41),esk2_0))&~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])])).
% 34.16/34.38  fof(c_0_27, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_relset_1(X20,X21,X22)=k1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 34.16/34.38  cnf(c_0_28, plain, (k2_relset_1(X1,X2,k2_relat_1(k1_xboole_0))=k2_relat_1(k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_18, c_0_23])).
% 34.16/34.38  cnf(c_0_29, plain, (k2_relset_1(X1,X2,k2_relset_1(X3,k2_zfmisc_1(X1,X2),X4))=k2_relat_1(k2_relset_1(X3,k2_zfmisc_1(X1,X2),X4))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 34.16/34.38  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk1_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 34.16/34.38  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 34.16/34.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 34.16/34.38  fof(c_0_33, plain, ![X26, X27, X28]:((((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&((~v1_funct_2(X28,X26,X27)|X28=k1_xboole_0|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X28!=k1_xboole_0|v1_funct_2(X28,X26,X27)|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 34.16/34.38  cnf(c_0_34, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 34.16/34.38  fof(c_0_35, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 34.16/34.38  cnf(c_0_36, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_28]), c_0_23])])).
% 34.16/34.38  cnf(c_0_37, plain, (k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k1_xboole_0)))=k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_28]), c_0_28])).
% 34.16/34.38  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_30])).
% 34.16/34.38  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 34.16/34.38  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 34.16/34.38  cnf(c_0_41, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 34.16/34.38  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 34.16/34.38  cnf(c_0_43, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 34.16/34.38  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 34.16/34.38  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 34.16/34.38  cnf(c_0_46, plain, (k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))=k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_37]), c_0_37])).
% 34.16/34.38  cnf(c_0_47, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_37]), c_0_36])])).
% 34.16/34.38  fof(c_0_48, plain, ![X29, X30, X31, X32]:(v1_xboole_0(X29)|~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,X29)|k3_funct_2(X29,X30,X31,X32)=k1_funct_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 34.16/34.38  fof(c_0_49, plain, ![X10, X11]:(~r2_hidden(X10,X11)|m1_subset_1(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 34.16/34.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1)))|r2_hidden(esk1_3(k1_relat_1(esk5_0),X1,esk5_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 34.16/34.38  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_32])])).
% 34.16/34.38  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_16])).
% 34.16/34.38  cnf(c_0_53, plain, (r1_tarski(k2_relset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_20])).
% 34.16/34.38  cnf(c_0_54, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_46]), c_0_47])])).
% 34.16/34.38  cnf(c_0_55, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 34.16/34.38  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 34.16/34.38  cnf(c_0_57, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 34.16/34.38  cnf(c_0_58, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|r2_hidden(esk1_3(esk3_0,X1,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 34.16/34.38  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_52])).
% 34.16/34.38  cnf(c_0_60, plain, (r1_tarski(k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))),X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 34.16/34.38  cnf(c_0_61, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_42]), c_0_40]), c_0_32])]), c_0_56])).
% 34.16/34.38  cnf(c_0_62, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|m1_subset_1(esk1_3(esk3_0,X1,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 34.16/34.38  cnf(c_0_63, plain, (k2_relset_1(X1,X2,k2_relset_1(X3,k2_zfmisc_1(X1,X2),k2_relset_1(X4,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)),X5)))=k2_relat_1(k2_relset_1(X3,k2_zfmisc_1(X1,X2),k2_relset_1(X4,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)),X5)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)))))), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 34.16/34.38  cnf(c_0_64, plain, (k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))=k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_47]), c_0_46]), c_0_46])).
% 34.16/34.38  cnf(c_0_65, plain, (m1_subset_1(k2_relset_1(X1,k1_xboole_0,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 34.16/34.38  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(k1_funct_1(X1,esk1_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 34.16/34.38  cnf(c_0_67, negated_conjecture, (r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X1),esk2_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 34.16/34.38  cnf(c_0_68, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))|esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 34.16/34.38  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_32])).
% 34.16/34.38  cnf(c_0_70, negated_conjecture, (r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_32])).
% 34.16/34.38  cnf(c_0_71, plain, (k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))=k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_47]), c_0_46]), c_0_64]), c_0_46]), c_0_64])).
% 34.16/34.38  cnf(c_0_72, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_64])).
% 34.16/34.38  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,esk1_3(k1_relat_1(X1),X2,X1)),X2)), inference(er,[status(thm)],[c_0_66])).
% 34.16/34.38  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0)), inference(spm,[status(thm)],[c_0_67, c_0_62])).
% 34.16/34.38  cnf(c_0_75, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))|k2_relset_1(esk3_0,X1,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_68]), c_0_69])).
% 34.16/34.38  cnf(c_0_76, negated_conjecture, (~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 34.16/34.38  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_70])).
% 34.16/34.38  cnf(c_0_78, plain, (k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))))=k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_54]), c_0_64]), c_0_71]), c_0_64]), c_0_71])).
% 34.16/34.38  cnf(c_0_79, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))))),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_71]), c_0_72])])).
% 34.16/34.38  cnf(c_0_80, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_40]), c_0_39])])).
% 34.16/34.38  cnf(c_0_81, negated_conjecture, (k2_relset_1(esk3_0,X1,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 34.16/34.38  cnf(c_0_82, negated_conjecture, (~r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 34.16/34.38  cnf(c_0_83, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_78]), c_0_79])])).
% 34.16/34.38  cnf(c_0_84, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 34.16/34.38  cnf(c_0_85, negated_conjecture, (~r1_tarski(X1,esk2_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_44])).
% 34.16/34.38  cnf(c_0_86, plain, (r1_tarski(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))),X1)), inference(spm,[status(thm)],[c_0_45, c_0_83])).
% 34.16/34.38  cnf(c_0_87, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_84]), c_0_69])])).
% 34.16/34.38  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk4_0,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 34.16/34.38  cnf(c_0_89, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))|esk4_0=k1_xboole_0|r1_tarski(k2_relset_1(esk3_0,X1,esk5_0),X1)), inference(spm,[status(thm)],[c_0_53, c_0_68])).
% 34.16/34.38  cnf(c_0_90, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_20, c_0_87])).
% 34.16/34.38  cnf(c_0_91, negated_conjecture, (~r1_tarski(esk4_0,k2_relset_1(X1,X2,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))))), inference(spm,[status(thm)],[c_0_88, c_0_78])).
% 34.16/34.38  cnf(c_0_92, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk2_0,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,esk2_0,esk5_0))|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_87]), c_0_76])).
% 34.16/34.38  cnf(c_0_93, negated_conjecture, (esk4_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_90]), c_0_76])).
% 34.16/34.38  cnf(c_0_94, negated_conjecture, (~r1_tarski(esk4_0,k2_relset_1(X1,X2,k2_relset_1(X3,X4,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))))))), inference(spm,[status(thm)],[c_0_91, c_0_71])).
% 34.16/34.38  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_92]), c_0_80]), c_0_93])).
% 34.16/34.38  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95]), c_0_16])]), ['proof']).
% 34.16/34.38  # SZS output end CNFRefutation
% 34.16/34.38  # Proof object total steps             : 97
% 34.16/34.38  # Proof object clause steps            : 72
% 34.16/34.38  # Proof object formula steps           : 25
% 34.16/34.38  # Proof object conjectures             : 37
% 34.16/34.38  # Proof object clause conjectures      : 34
% 34.16/34.38  # Proof object formula conjectures     : 3
% 34.16/34.38  # Proof object initial clauses used    : 19
% 34.16/34.38  # Proof object initial formulas used   : 12
% 34.16/34.38  # Proof object generating inferences   : 50
% 34.16/34.39  # Proof object simplifying inferences  : 50
% 34.16/34.39  # Training examples: 0 positive, 0 negative
% 34.16/34.39  # Parsed axioms                        : 12
% 34.16/34.39  # Removed by relevancy pruning/SinE    : 0
% 34.16/34.39  # Initial clauses                      : 29
% 34.16/34.39  # Removed in clause preprocessing      : 2
% 34.16/34.39  # Initial clauses in saturation        : 27
% 34.16/34.39  # Processed clauses                    : 137096
% 34.16/34.39  # ...of these trivial                  : 1621
% 34.16/34.39  # ...subsumed                          : 129933
% 34.16/34.39  # ...remaining for further processing  : 5542
% 34.16/34.39  # Other redundant clauses eliminated   : 31
% 34.16/34.39  # Clauses deleted for lack of memory   : 0
% 34.16/34.39  # Backward-subsumed                    : 1043
% 34.16/34.39  # Backward-rewritten                   : 3902
% 34.16/34.39  # Generated clauses                    : 2082223
% 34.16/34.39  # ...of the previous two non-trivial   : 2037530
% 34.16/34.39  # Contextual simplify-reflections      : 28
% 34.16/34.39  # Paramodulations                      : 2082193
% 34.16/34.39  # Factorizations                       : 0
% 34.16/34.39  # Equation resolutions                 : 31
% 34.16/34.39  # Propositional unsat checks           : 0
% 34.16/34.39  #    Propositional check models        : 0
% 34.16/34.39  #    Propositional check unsatisfiable : 0
% 34.16/34.39  #    Propositional clauses             : 0
% 34.16/34.39  #    Propositional clauses after purity: 0
% 34.16/34.39  #    Propositional unsat core size     : 0
% 34.16/34.39  #    Propositional preprocessing time  : 0.000
% 34.16/34.39  #    Propositional encoding time       : 0.000
% 34.16/34.39  #    Propositional solver time         : 0.000
% 34.16/34.39  #    Success case prop preproc time    : 0.000
% 34.16/34.39  #    Success case prop encoding time   : 0.000
% 34.16/34.39  #    Success case prop solver time     : 0.000
% 34.16/34.39  # Current number of processed clauses  : 562
% 34.16/34.39  #    Positive orientable unit clauses  : 248
% 34.16/34.39  #    Positive unorientable unit clauses: 28
% 34.16/34.39  #    Negative unit clauses             : 1
% 34.16/34.39  #    Non-unit-clauses                  : 285
% 34.16/34.39  # Current number of unprocessed clauses: 1878318
% 34.16/34.39  # ...number of literals in the above   : 14631570
% 34.16/34.39  # Current number of archived formulas  : 0
% 34.16/34.39  # Current number of archived clauses   : 4972
% 34.16/34.39  # Clause-clause subsumption calls (NU) : 50788836
% 34.16/34.39  # Rec. Clause-clause subsumption calls : 3036522
% 34.16/34.39  # Non-unit clause-clause subsumptions  : 94843
% 34.16/34.39  # Unit Clause-clause subsumption calls : 389153
% 34.16/34.39  # Rewrite failures with RHS unbound    : 1175
% 34.16/34.39  # BW rewrite match attempts            : 12714
% 34.16/34.39  # BW rewrite match successes           : 432
% 34.16/34.39  # Condensation attempts                : 0
% 34.16/34.39  # Condensation successes               : 0
% 34.16/34.39  # Termbank termtop insertions          : 46485873
% 34.26/34.46  
% 34.26/34.46  # -------------------------------------------------
% 34.26/34.46  # User time                : 33.303 s
% 34.26/34.46  # System time              : 0.811 s
% 34.26/34.46  # Total time               : 34.113 s
% 34.26/34.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
