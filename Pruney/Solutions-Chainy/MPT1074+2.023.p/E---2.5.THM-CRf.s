%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 556 expanded)
%              Number of clauses        :   43 ( 222 expanded)
%              Number of leaves         :   12 ( 134 expanded)
%              Depth                    :   16
%              Number of atoms          :  241 (2947 expanded)
%              Number of equality atoms :   67 ( 413 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k1_relset_1(X17,X18,X19) = k1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_14,negated_conjecture,(
    ! [X38] :
      ( ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X38,esk3_0)
        | r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X38),esk2_0) )
      & ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X30,X31,X32] :
      ( ( v1_funct_1(X32)
        | r2_hidden(esk1_3(X30,X31,X32),X30)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_2(X32,X30,X31)
        | r2_hidden(esk1_3(X30,X31,X32),X30)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | r2_hidden(esk1_3(X30,X31,X32),X30)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_1(X32)
        | ~ r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_2(X32,X30,X31)
        | ~ r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X25 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != k1_xboole_0
        | v1_funct_2(X25,X23,X24)
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_19,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X26,X27,X28,X29] :
      ( v1_xboole_0(X26)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,X26,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ m1_subset_1(X29,X26)
      | k3_funct_2(X26,X27,X28,X29) = k1_funct_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_29,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | r2_hidden(esk1_3(esk3_0,X1,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

fof(c_0_38,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k2_relset_1(X20,X21,X22) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_39,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_32]),c_0_20])]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(k1_relat_1(X1),X2,X1)),X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))
    | k2_relset_1(esk3_0,X1,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_44]),c_0_45])).

fof(c_0_49,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_50,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | m1_subset_1(k2_relset_1(X14,X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(esk3_0,X1,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_relset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = k2_relset_1(esk3_0,esk4_0,esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_55]),c_0_45])])).

cnf(c_0_58,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))
    | esk4_0 = k1_xboole_0
    | r1_tarski(k2_relset_1(esk3_0,X1,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk2_0,esk5_0)) = k1_funct_1(esk5_0,esk1_3(esk3_0,esk2_0,esk5_0))
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_60]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_61]),c_0_51]),c_0_62])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.41  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.039 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t191_funct_2, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.20/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.20/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.41  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1)))))), inference(assume_negation,[status(cth)],[t191_funct_2])).
% 0.20/0.41  fof(c_0_13, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|k1_relset_1(X17,X18,X19)=k1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ![X38]:(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((~m1_subset_1(X38,esk3_0)|r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X38),esk2_0))&~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.20/0.41  fof(c_0_15, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.41  fof(c_0_16, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  fof(c_0_17, plain, ![X30, X31, X32]:((((v1_funct_1(X32)|(r2_hidden(esk1_3(X30,X31,X32),X30)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_2(X32,X30,X31)|(r2_hidden(esk1_3(X30,X31,X32),X30)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(r2_hidden(esk1_3(X30,X31,X32),X30)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(((v1_funct_1(X32)|(~r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_2(X32,X30,X31)|(~r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(~r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.41  fof(c_0_18, plain, ![X23, X24, X25]:((((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))&((~v1_funct_2(X25,X23,X24)|X25=k1_xboole_0|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X25!=k1_xboole_0|v1_funct_2(X25,X23,X24)|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  cnf(c_0_19, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk1_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_24, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.41  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  fof(c_0_28, plain, ![X26, X27, X28, X29]:(v1_xboole_0(X26)|~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,X26)|k3_funct_2(X26,X27,X28,X29)=k1_funct_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.20/0.41  fof(c_0_29, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.41  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_20])])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_20])).
% 0.20/0.41  cnf(c_0_34, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_36, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|r2_hidden(esk1_3(esk3_0,X1,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 0.20/0.41  fof(c_0_38, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k2_relset_1(X20,X21,X22)=k2_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_32]), c_0_20])]), c_0_35])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|m1_subset_1(esk1_3(esk3_0,X1,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_41, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(k1_funct_1(X1,esk1_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X1),esk2_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))|esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 0.20/0.41  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,esk1_3(k1_relat_1(X1),X2,X1)),X2)), inference(er,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))|k2_relset_1(esk3_0,X1,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_44]), c_0_45])).
% 0.20/0.41  fof(c_0_49, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_50, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|m1_subset_1(k2_relset_1(X14,X15,X16),k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_32]), c_0_33])])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (k2_relset_1(esk3_0,X1,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0)),esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_54, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.41  cnf(c_0_56, plain, (r1_tarski(k2_relset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=k2_relset_1(esk3_0,esk4_0,esk5_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_55]), c_0_45])])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,X1,esk5_0))|esk4_0=k1_xboole_0|r1_tarski(k2_relset_1(esk3_0,X1,esk5_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_44])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_54, c_0_57])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk2_0,esk5_0))=k1_funct_1(esk5_0,esk1_3(esk3_0,esk2_0,esk5_0))|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_57]), c_0_59])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (esk4_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_60]), c_0_59])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_61]), c_0_51]), c_0_62])).
% 0.20/0.41  cnf(c_0_65, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 67
% 0.20/0.41  # Proof object clause steps            : 43
% 0.20/0.41  # Proof object formula steps           : 24
% 0.20/0.41  # Proof object conjectures             : 30
% 0.20/0.41  # Proof object clause conjectures      : 27
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 19
% 0.20/0.41  # Proof object initial formulas used   : 12
% 0.20/0.41  # Proof object generating inferences   : 21
% 0.20/0.41  # Proof object simplifying inferences  : 25
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 12
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 29
% 0.20/0.41  # Removed in clause preprocessing      : 2
% 0.20/0.41  # Initial clauses in saturation        : 27
% 0.20/0.41  # Processed clauses                    : 157
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 19
% 0.20/0.41  # ...remaining for further processing  : 138
% 0.20/0.41  # Other redundant clauses eliminated   : 9
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 9
% 0.20/0.41  # Backward-rewritten                   : 55
% 0.20/0.41  # Generated clauses                    : 201
% 0.20/0.41  # ...of the previous two non-trivial   : 193
% 0.20/0.41  # Contextual simplify-reflections      : 10
% 0.20/0.41  # Paramodulations                      : 193
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 9
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
% 0.20/0.41  # Current number of processed clauses  : 39
% 0.20/0.41  #    Positive orientable unit clauses  : 5
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 33
% 0.20/0.41  # Current number of unprocessed clauses: 65
% 0.20/0.41  # ...number of literals in the above   : 279
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 91
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1570
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 566
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 38
% 0.20/0.41  # Unit Clause-clause subsumption calls : 24
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 1
% 0.20/0.41  # BW rewrite match successes           : 1
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 7146
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.055 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.063 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
