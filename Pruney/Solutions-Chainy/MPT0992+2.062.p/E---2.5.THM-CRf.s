%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:43 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  158 (5451 expanded)
%              Number of clauses        :  101 (2306 expanded)
%              Number of leaves         :   28 (1342 expanded)
%              Depth                    :   23
%              Number of atoms          :  449 (21979 expanded)
%              Number of equality atoms :   87 (6867 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t4_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ( r1_tarski(X1,X4)
       => m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X3,X1)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
              & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
              & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_2])).

fof(c_0_29,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk3_0,esk1_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_31,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
    | ~ r1_tarski(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X65,X66,X67,X68] :
      ( ~ v1_funct_1(X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | k2_partfun1(X65,X66,X67,X68) = k7_relat_1(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0))
    | ~ r1_tarski(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_50,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_33]),c_0_44])).

fof(c_0_53,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | r1_tarski(k7_relat_1(X38,X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ v1_funct_1(k7_relat_1(esk4_0,k1_xboole_0))
    | ~ r1_tarski(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_41])])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

fof(c_0_64,plain,(
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

cnf(c_0_65,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ v1_funct_1(k7_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_60]),c_0_61])])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

fof(c_0_70,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_relset_1(X51,X52,X53) = k1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_71,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_66]),c_0_66]),c_0_67])]),c_0_68]),c_0_69])).

fof(c_0_73,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | v1_relat_1(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_74,plain,(
    ! [X48,X49,X50] :
      ( ( v4_relat_1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v5_relat_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_75,plain,(
    ! [X19,X20] :
      ( ( ~ v4_relat_1(X20,X19)
        | r1_tarski(k1_relat_1(X20),X19)
        | ~ v1_relat_1(X20) )
      & ( ~ r1_tarski(k1_relat_1(X20),X19)
        | v4_relat_1(X20,X19)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_76,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_57])]),c_0_72])).

cnf(c_0_78,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_79,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v4_relat_1(X34,X33)
      | X34 = k7_relat_1(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_80,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_81,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_82,plain,(
    ! [X25,X26,X27] :
      ( ( v1_relat_1(k7_relat_1(X27,X25))
        | ~ v1_relat_1(X27)
        | ~ v4_relat_1(X27,X26) )
      & ( v4_relat_1(k7_relat_1(X27,X25),X25)
        | ~ v1_relat_1(X27)
        | ~ v4_relat_1(X27,X26) )
      & ( v4_relat_1(k7_relat_1(X27,X25),X26)
        | ~ v1_relat_1(X27)
        | ~ v4_relat_1(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

cnf(c_0_83,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_41])])).

cnf(c_0_85,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_41]),c_0_54])])).

fof(c_0_86,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | r1_tarski(k1_relat_1(k7_relat_1(X36,X35)),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_87,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( v4_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_41])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( v4_relat_1(esk4_0,X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_92,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(esk4_0,esk1_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_85])])).

cnf(c_0_94,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_46])).

fof(c_0_96,plain,(
    ! [X58,X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | ~ r1_tarski(X58,X61)
      | m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).

fof(c_0_97,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k7_relat_1(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_98,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk4_0,X1),X1)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_85])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_85])]),c_0_84])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_54])])).

fof(c_0_101,plain,(
    ! [X54,X55,X56,X57] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X56)))
      | ~ r1_tarski(k1_relat_1(X57),X55)
      | m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_102,plain,
    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_103,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | r1_tarski(k1_relat_1(k7_relat_1(X40,X39)),k1_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k7_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_60])).

cnf(c_0_105,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_60]),c_0_85])])).

fof(c_0_108,plain,(
    ! [X46,X47] :
      ( ( v1_relat_1(k7_relat_1(X46,X47))
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( v1_funct_1(k7_relat_1(X46,X47))
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_109,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(X30,X31)
      | k7_relat_1(k7_relat_1(X32,X31),X30) = k7_relat_1(X32,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

fof(c_0_110,plain,(
    ! [X21,X22] :
      ( ( ~ v5_relat_1(X22,X21)
        | r1_tarski(k2_relat_1(X22),X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r1_tarski(k2_relat_1(X22),X21)
        | v5_relat_1(X22,X21)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_111,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | r1_tarski(k2_relat_1(k7_relat_1(X45,X44)),k2_relat_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

cnf(c_0_112,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_41])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_60]),c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,X1),X1) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_106]),c_0_107])])).

fof(c_0_117,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ r1_tarski(X41,k1_relat_1(X42))
      | k1_relat_1(k7_relat_1(X42,X41)) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_118,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_119,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_120,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_121,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_84]),c_0_85])])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_85])])).

cnf(c_0_125,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_126,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_127,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_105])).

cnf(c_0_128,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = esk4_0
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_91]),c_0_85])])).

fof(c_0_129,plain,(
    ! [X43] :
      ( ~ v1_relat_1(X43)
      | k7_relat_1(X43,k1_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_130,plain,
    ( r1_tarski(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_120])).

cnf(c_0_131,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_119]),c_0_105])).

cnf(c_0_132,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124])])).

cnf(c_0_134,plain,
    ( r1_tarski(X1,X2)
    | ~ v4_relat_1(k7_relat_1(X3,X1),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_105])).

cnf(c_0_135,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,X1))
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_51]),c_0_85])])).

cnf(c_0_136,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

fof(c_0_137,plain,(
    ! [X69,X70] :
      ( ( v1_funct_1(X70)
        | ~ r1_tarski(k2_relat_1(X70),X69)
        | ~ v1_relat_1(X70)
        | ~ v1_funct_1(X70) )
      & ( v1_funct_2(X70,k1_relat_1(X70),X69)
        | ~ r1_tarski(k2_relat_1(X70),X69)
        | ~ v1_relat_1(X70)
        | ~ v1_funct_1(X70) )
      & ( m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X70),X69)))
        | ~ r1_tarski(k2_relat_1(X70),X69)
        | ~ v1_relat_1(X70)
        | ~ v1_funct_1(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_138,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ v5_relat_1(k7_relat_1(X1,X4),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_105])).

cnf(c_0_139,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_106]),c_0_85]),c_0_84])])).

cnf(c_0_141,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k7_relat_1(esk4_0,esk3_0))
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_50]),c_0_51]),c_0_41])])).

cnf(c_0_142,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,X1))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_99])).

cnf(c_0_143,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_119]),c_0_92]),c_0_105])).

cnf(c_0_144,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_85])])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_32])).

cnf(c_0_147,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_148,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k7_relat_1(esk4_0,esk3_0))
    | ~ r1_tarski(k7_relat_1(esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_36])).

cnf(c_0_149,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_123]),c_0_85])])).

cnf(c_0_150,plain,
    ( v1_funct_2(k7_relat_1(X1,X2),X2,X3)
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_126]),c_0_105])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_152,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ r1_tarski(k7_relat_1(esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_149])])).

cnf(c_0_154,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_149]),c_0_85]),c_0_84]),c_0_32])])).

cnf(c_0_155,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_126]),c_0_105])).

cnf(c_0_156,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_154])])).

cnf(c_0_157,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_151]),c_0_149]),c_0_85]),c_0_84]),c_0_32])]),c_0_156]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.83  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.62/0.83  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.62/0.83  #
% 0.62/0.83  # Preprocessing time       : 0.029 s
% 0.62/0.83  # Presaturation interreduction done
% 0.62/0.83  
% 0.62/0.83  # Proof found!
% 0.62/0.83  # SZS status Theorem
% 0.62/0.83  # SZS output start CNFRefutation
% 0.62/0.83  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 0.62/0.83  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.62/0.83  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.62/0.83  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.62/0.83  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.62/0.83  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.62/0.83  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.62/0.83  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.62/0.83  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.62/0.83  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.62/0.83  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.62/0.83  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.62/0.83  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.62/0.83  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.62/0.83  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.62/0.83  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.62/0.83  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.62/0.83  fof(t4_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>(r1_tarski(X1,X4)=>m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 0.62/0.83  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.62/0.83  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 0.62/0.83  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 0.62/0.83  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.62/0.83  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 0.62/0.83  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.62/0.83  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 0.62/0.83  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.62/0.83  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.62/0.83  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.62/0.83  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 0.62/0.83  fof(c_0_29, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk3_0,esk1_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.62/0.83  fof(c_0_30, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.62/0.83  fof(c_0_31, plain, ![X8]:(~r1_tarski(X8,k1_xboole_0)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.62/0.83  cnf(c_0_32, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.83  cnf(c_0_33, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.83  fof(c_0_34, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.62/0.83  cnf(c_0_35, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.83  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.83  cnf(c_0_37, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.62/0.83  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.62/0.83  cnf(c_0_39, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.62/0.83  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.83  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.83  cnf(c_0_42, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~r1_tarski(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.62/0.83  cnf(c_0_43, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.62/0.83  cnf(c_0_44, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_39])).
% 0.62/0.83  fof(c_0_45, plain, ![X65, X66, X67, X68]:(~v1_funct_1(X67)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|k2_partfun1(X65,X66,X67,X68)=k7_relat_1(X67,X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.62/0.83  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.62/0.83  fof(c_0_47, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.62/0.83  cnf(c_0_48, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.62/0.83  cnf(c_0_49, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0))|~r1_tarski(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.62/0.83  cnf(c_0_50, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.62/0.83  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.83  cnf(c_0_52, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_33]), c_0_44])).
% 0.62/0.83  fof(c_0_53, plain, ![X37, X38]:(~v1_relat_1(X38)|r1_tarski(k7_relat_1(X38,X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.62/0.83  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.62/0.83  cnf(c_0_55, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_48])).
% 0.62/0.83  fof(c_0_56, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.62/0.83  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.83  cnf(c_0_58, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~v1_funct_1(k7_relat_1(esk4_0,k1_xboole_0))|~r1_tarski(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_41])])).
% 0.62/0.83  cnf(c_0_59, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_52])).
% 0.62/0.83  cnf(c_0_60, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.62/0.83  cnf(c_0_61, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.62/0.83  cnf(c_0_62, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.62/0.83  cnf(c_0_63, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.62/0.83  fof(c_0_64, plain, ![X62, X63, X64]:((((~v1_funct_2(X64,X62,X63)|X62=k1_relset_1(X62,X63,X64)|X63=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(X62!=k1_relset_1(X62,X63,X64)|v1_funct_2(X64,X62,X63)|X63=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&((~v1_funct_2(X64,X62,X63)|X62=k1_relset_1(X62,X63,X64)|X62!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(X62!=k1_relset_1(X62,X63,X64)|v1_funct_2(X64,X62,X63)|X62!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&((~v1_funct_2(X64,X62,X63)|X64=k1_xboole_0|X62=k1_xboole_0|X63!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(X64!=k1_xboole_0|v1_funct_2(X64,X62,X63)|X62=k1_xboole_0|X63!=k1_xboole_0|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.62/0.83  cnf(c_0_65, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)|~v1_funct_1(k7_relat_1(k1_xboole_0,k1_xboole_0))|~r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.62/0.83  cnf(c_0_66, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_60]), c_0_61])])).
% 0.62/0.83  cnf(c_0_67, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_62])).
% 0.62/0.83  cnf(c_0_68, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_59])).
% 0.62/0.83  cnf(c_0_69, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.62/0.83  fof(c_0_70, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_relset_1(X51,X52,X53)=k1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.62/0.83  cnf(c_0_71, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.62/0.83  cnf(c_0_72, negated_conjecture, (esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_66]), c_0_66]), c_0_67])]), c_0_68]), c_0_69])).
% 0.62/0.83  fof(c_0_73, plain, ![X17, X18]:(~v1_relat_1(X17)|(~m1_subset_1(X18,k1_zfmisc_1(X17))|v1_relat_1(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.62/0.83  fof(c_0_74, plain, ![X48, X49, X50]:((v4_relat_1(X50,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v5_relat_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.62/0.83  fof(c_0_75, plain, ![X19, X20]:((~v4_relat_1(X20,X19)|r1_tarski(k1_relat_1(X20),X19)|~v1_relat_1(X20))&(~r1_tarski(k1_relat_1(X20),X19)|v4_relat_1(X20,X19)|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.62/0.83  cnf(c_0_76, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.62/0.83  cnf(c_0_77, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_57])]), c_0_72])).
% 0.62/0.83  cnf(c_0_78, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.62/0.83  fof(c_0_79, plain, ![X33, X34]:(~v1_relat_1(X34)|~v4_relat_1(X34,X33)|X34=k7_relat_1(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.62/0.83  cnf(c_0_80, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.62/0.83  fof(c_0_81, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.62/0.83  fof(c_0_82, plain, ![X25, X26, X27]:(((v1_relat_1(k7_relat_1(X27,X25))|(~v1_relat_1(X27)|~v4_relat_1(X27,X26)))&(v4_relat_1(k7_relat_1(X27,X25),X25)|(~v1_relat_1(X27)|~v4_relat_1(X27,X26))))&(v4_relat_1(k7_relat_1(X27,X25),X26)|(~v1_relat_1(X27)|~v4_relat_1(X27,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.62/0.83  cnf(c_0_83, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.62/0.83  cnf(c_0_84, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_41])])).
% 0.62/0.83  cnf(c_0_85, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_41]), c_0_54])])).
% 0.62/0.83  fof(c_0_86, plain, ![X35, X36]:(~v1_relat_1(X36)|r1_tarski(k1_relat_1(k7_relat_1(X36,X35)),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.62/0.83  cnf(c_0_87, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.62/0.83  cnf(c_0_88, negated_conjecture, (v4_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_80, c_0_41])).
% 0.62/0.83  cnf(c_0_89, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.62/0.83  cnf(c_0_90, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.62/0.83  cnf(c_0_91, negated_conjecture, (v4_relat_1(esk4_0,X1)|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])])).
% 0.62/0.83  cnf(c_0_92, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.62/0.83  cnf(c_0_93, negated_conjecture, (k7_relat_1(esk4_0,esk1_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_85])])).
% 0.62/0.83  cnf(c_0_94, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_36])).
% 0.62/0.83  cnf(c_0_95, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_89, c_0_46])).
% 0.62/0.83  fof(c_0_96, plain, ![X58, X59, X60, X61]:(~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|(~r1_tarski(X58,X61)|m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).
% 0.62/0.83  fof(c_0_97, plain, ![X23, X24]:(~v1_relat_1(X23)|v1_relat_1(k7_relat_1(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.62/0.83  cnf(c_0_98, negated_conjecture, (v4_relat_1(k7_relat_1(esk4_0,X1),X1)|~r1_tarski(esk1_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_85])])).
% 0.62/0.83  cnf(c_0_99, negated_conjecture, (r1_tarski(esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_85])]), c_0_84])).
% 0.62/0.83  cnf(c_0_100, negated_conjecture, (v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_54])])).
% 0.62/0.83  fof(c_0_101, plain, ![X54, X55, X56, X57]:(~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X56)))|(~r1_tarski(k1_relat_1(X57),X55)|m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.62/0.83  cnf(c_0_102, plain, (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.62/0.83  fof(c_0_103, plain, ![X39, X40]:(~v1_relat_1(X40)|r1_tarski(k1_relat_1(k7_relat_1(X40,X39)),k1_relat_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.62/0.83  cnf(c_0_104, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k7_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_89, c_0_60])).
% 0.62/0.83  cnf(c_0_105, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.62/0.83  cnf(c_0_106, negated_conjecture, (v4_relat_1(k7_relat_1(esk4_0,X1),X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.62/0.83  cnf(c_0_107, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_60]), c_0_85])])).
% 0.62/0.83  fof(c_0_108, plain, ![X46, X47]:((v1_relat_1(k7_relat_1(X46,X47))|(~v1_relat_1(X46)|~v1_funct_1(X46)))&(v1_funct_1(k7_relat_1(X46,X47))|(~v1_relat_1(X46)|~v1_funct_1(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.62/0.83  fof(c_0_109, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(X30,X31)|k7_relat_1(k7_relat_1(X32,X31),X30)=k7_relat_1(X32,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.62/0.83  fof(c_0_110, plain, ![X21, X22]:((~v5_relat_1(X22,X21)|r1_tarski(k2_relat_1(X22),X21)|~v1_relat_1(X22))&(~r1_tarski(k2_relat_1(X22),X21)|v5_relat_1(X22,X21)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.62/0.83  fof(c_0_111, plain, ![X44, X45]:(~v1_relat_1(X45)|r1_tarski(k2_relat_1(k7_relat_1(X45,X44)),k2_relat_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 0.62/0.83  cnf(c_0_112, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.62/0.83  cnf(c_0_113, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_102, c_0_41])).
% 0.62/0.83  cnf(c_0_114, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.62/0.83  cnf(c_0_115, plain, (r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_60]), c_0_105])).
% 0.62/0.83  cnf(c_0_116, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,X1),X1)=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_106]), c_0_107])])).
% 0.62/0.83  fof(c_0_117, plain, ![X41, X42]:(~v1_relat_1(X42)|(~r1_tarski(X41,k1_relat_1(X42))|k1_relat_1(k7_relat_1(X42,X41))=X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.62/0.83  cnf(c_0_118, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.62/0.83  cnf(c_0_119, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.62/0.83  cnf(c_0_120, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.62/0.83  cnf(c_0_121, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.62/0.83  cnf(c_0_122, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.62/0.83  cnf(c_0_123, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_84]), c_0_85])])).
% 0.62/0.83  cnf(c_0_124, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_85])])).
% 0.62/0.83  cnf(c_0_125, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.62/0.83  cnf(c_0_126, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.62/0.83  cnf(c_0_127, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_funct_1(k7_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_105])).
% 0.62/0.83  cnf(c_0_128, negated_conjecture, (k7_relat_1(esk4_0,X1)=esk4_0|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_91]), c_0_85])])).
% 0.62/0.83  fof(c_0_129, plain, ![X43]:(~v1_relat_1(X43)|k7_relat_1(X43,k1_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.62/0.83  cnf(c_0_130, plain, (r1_tarski(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_89, c_0_120])).
% 0.62/0.83  cnf(c_0_131, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X3)))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_119]), c_0_105])).
% 0.62/0.83  cnf(c_0_132, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.62/0.83  cnf(c_0_133, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124])])).
% 0.62/0.83  cnf(c_0_134, plain, (r1_tarski(X1,X2)|~v4_relat_1(k7_relat_1(X3,X1),X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_105])).
% 0.62/0.83  cnf(c_0_135, negated_conjecture, (v1_funct_1(k7_relat_1(esk4_0,X1))|~r1_tarski(esk1_0,X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_51]), c_0_85])])).
% 0.62/0.83  cnf(c_0_136, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.62/0.83  fof(c_0_137, plain, ![X69, X70]:(((v1_funct_1(X70)|~r1_tarski(k2_relat_1(X70),X69)|(~v1_relat_1(X70)|~v1_funct_1(X70)))&(v1_funct_2(X70,k1_relat_1(X70),X69)|~r1_tarski(k2_relat_1(X70),X69)|(~v1_relat_1(X70)|~v1_funct_1(X70))))&(m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X70),X69)))|~r1_tarski(k2_relat_1(X70),X69)|(~v1_relat_1(X70)|~v1_funct_1(X70)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.62/0.83  cnf(c_0_138, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)|~v5_relat_1(k7_relat_1(X1,X4),X3)|~v1_relat_1(X1)|~r1_tarski(X2,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_105])).
% 0.62/0.83  cnf(c_0_139, negated_conjecture, (v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 0.62/0.83  cnf(c_0_140, negated_conjecture, (r1_tarski(X1,X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_106]), c_0_85]), c_0_84])])).
% 0.62/0.83  cnf(c_0_141, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~v1_funct_1(k7_relat_1(esk4_0,esk3_0))|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_50]), c_0_51]), c_0_41])])).
% 0.62/0.83  cnf(c_0_142, negated_conjecture, (v1_funct_1(k7_relat_1(esk4_0,X1))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_135, c_0_99])).
% 0.62/0.83  cnf(c_0_143, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_119]), c_0_92]), c_0_105])).
% 0.62/0.83  cnf(c_0_144, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.62/0.83  cnf(c_0_145, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_85])])).
% 0.62/0.83  cnf(c_0_146, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_140, c_0_32])).
% 0.62/0.83  cnf(c_0_147, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.62/0.83  cnf(c_0_148, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~v1_funct_1(k7_relat_1(esk4_0,esk3_0))|~r1_tarski(k7_relat_1(esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_141, c_0_36])).
% 0.62/0.83  cnf(c_0_149, negated_conjecture, (v1_funct_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_123]), c_0_85])])).
% 0.62/0.83  cnf(c_0_150, plain, (v1_funct_2(k7_relat_1(X1,X2),X2,X3)|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_126]), c_0_105])).
% 0.62/0.83  cnf(c_0_151, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_145, c_0_146])).
% 0.62/0.83  cnf(c_0_152, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_40, c_0_147])).
% 0.62/0.83  cnf(c_0_153, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~r1_tarski(k7_relat_1(esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_149])])).
% 0.62/0.83  cnf(c_0_154, negated_conjecture, (v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_149]), c_0_85]), c_0_84]), c_0_32])])).
% 0.62/0.83  cnf(c_0_155, plain, (r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(X2,X3))|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_126]), c_0_105])).
% 0.62/0.83  cnf(c_0_156, negated_conjecture, (~r1_tarski(k7_relat_1(esk4_0,esk3_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153, c_0_154])])).
% 0.62/0.83  cnf(c_0_157, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_151]), c_0_149]), c_0_85]), c_0_84]), c_0_32])]), c_0_156]), ['proof']).
% 0.62/0.83  # SZS output end CNFRefutation
% 0.62/0.83  # Proof object total steps             : 158
% 0.62/0.83  # Proof object clause steps            : 101
% 0.62/0.83  # Proof object formula steps           : 57
% 0.62/0.83  # Proof object conjectures             : 55
% 0.62/0.83  # Proof object clause conjectures      : 52
% 0.62/0.83  # Proof object formula conjectures     : 3
% 0.62/0.83  # Proof object initial clauses used    : 38
% 0.62/0.83  # Proof object initial formulas used   : 28
% 0.62/0.83  # Proof object generating inferences   : 58
% 0.62/0.83  # Proof object simplifying inferences  : 84
% 0.62/0.83  # Training examples: 0 positive, 0 negative
% 0.62/0.83  # Parsed axioms                        : 29
% 0.62/0.83  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.83  # Initial clauses                      : 50
% 0.62/0.83  # Removed in clause preprocessing      : 1
% 0.62/0.83  # Initial clauses in saturation        : 49
% 0.62/0.83  # Processed clauses                    : 7174
% 0.62/0.83  # ...of these trivial                  : 49
% 0.62/0.83  # ...subsumed                          : 5849
% 0.62/0.83  # ...remaining for further processing  : 1275
% 0.62/0.83  # Other redundant clauses eliminated   : 13
% 0.62/0.83  # Clauses deleted for lack of memory   : 0
% 0.62/0.83  # Backward-subsumed                    : 207
% 0.62/0.83  # Backward-rewritten                   : 40
% 0.62/0.83  # Generated clauses                    : 38977
% 0.62/0.83  # ...of the previous two non-trivial   : 33112
% 0.62/0.83  # Contextual simplify-reflections      : 198
% 0.62/0.83  # Paramodulations                      : 38965
% 0.62/0.83  # Factorizations                       : 0
% 0.62/0.83  # Equation resolutions                 : 13
% 0.62/0.83  # Propositional unsat checks           : 0
% 0.62/0.83  #    Propositional check models        : 0
% 0.62/0.83  #    Propositional check unsatisfiable : 0
% 0.62/0.83  #    Propositional clauses             : 0
% 0.62/0.83  #    Propositional clauses after purity: 0
% 0.62/0.83  #    Propositional unsat core size     : 0
% 0.62/0.83  #    Propositional preprocessing time  : 0.000
% 0.62/0.83  #    Propositional encoding time       : 0.000
% 0.62/0.83  #    Propositional solver time         : 0.000
% 0.62/0.83  #    Success case prop preproc time    : 0.000
% 0.62/0.83  #    Success case prop encoding time   : 0.000
% 0.62/0.83  #    Success case prop solver time     : 0.000
% 0.62/0.83  # Current number of processed clauses  : 975
% 0.62/0.83  #    Positive orientable unit clauses  : 61
% 0.62/0.83  #    Positive unorientable unit clauses: 0
% 0.62/0.83  #    Negative unit clauses             : 11
% 0.62/0.83  #    Non-unit-clauses                  : 903
% 0.62/0.83  # Current number of unprocessed clauses: 25589
% 0.62/0.83  # ...number of literals in the above   : 118306
% 0.62/0.83  # Current number of archived formulas  : 0
% 0.62/0.83  # Current number of archived clauses   : 294
% 0.62/0.83  # Clause-clause subsumption calls (NU) : 163111
% 0.62/0.83  # Rec. Clause-clause subsumption calls : 115048
% 0.62/0.83  # Non-unit clause-clause subsumptions  : 4183
% 0.62/0.83  # Unit Clause-clause subsumption calls : 2156
% 0.62/0.83  # Rewrite failures with RHS unbound    : 0
% 0.62/0.83  # BW rewrite match attempts            : 56
% 0.62/0.83  # BW rewrite match successes           : 22
% 0.62/0.83  # Condensation attempts                : 0
% 0.62/0.83  # Condensation successes               : 0
% 0.62/0.83  # Termbank termtop insertions          : 570363
% 0.62/0.83  
% 0.62/0.83  # -------------------------------------------------
% 0.62/0.83  # User time                : 0.469 s
% 0.62/0.83  # System time              : 0.024 s
% 0.62/0.83  # Total time               : 0.493 s
% 0.62/0.83  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
