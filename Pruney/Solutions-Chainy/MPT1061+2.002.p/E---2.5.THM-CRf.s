%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  166 (10737 expanded)
%              Number of clauses        :  116 (4608 expanded)
%              Number of leaves         :   25 (2633 expanded)
%              Depth                    :   24
%              Number of atoms          :  416 (44909 expanded)
%              Number of equality atoms :  102 (2829 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t178_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ~ v1_xboole_0(X4)
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X1,X4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k7_relset_1(X1,X4,X5,X2),X3) )
           => ( v1_funct_1(k2_partfun1(X1,X4,X5,X2))
              & v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3)
              & m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ~ v1_xboole_0(X4)
       => ! [X5] :
            ( ( v1_funct_1(X5)
              & v1_funct_2(X5,X1,X4)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k7_relset_1(X1,X4,X5,X2),X3) )
             => ( v1_funct_1(k2_partfun1(X1,X4,X5,X2))
                & v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3)
                & m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t178_funct_2])).

fof(c_0_26,plain,(
    ! [X41,X42,X43] :
      ( ( v4_relat_1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v5_relat_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk3_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk6_0)))
    & r1_tarski(esk4_0,esk3_0)
    & r1_tarski(k7_relset_1(esk3_0,esk6_0,esk7_0,esk4_0),esk5_0)
    & ( ~ v1_funct_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0))
      | ~ v1_funct_2(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk5_0)
      | ~ m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_28,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | v1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_29,plain,(
    ! [X26,X27] :
      ( ( ~ v4_relat_1(X27,X26)
        | r1_tarski(k1_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(k1_relat_1(X27),X26)
        | v4_relat_1(X27,X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_30,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X54,X55,X56] :
      ( ~ v1_relat_1(X56)
      | ~ r1_tarski(k1_relat_1(X56),X54)
      | ~ r1_tarski(k2_relat_1(X56),X55)
      | m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v4_relat_1(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_37,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X60,X61,X62] :
      ( ( v1_funct_1(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X61) )
      & ( v1_partfun1(X62,X60)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_42,plain,(
    ! [X66,X67,X68,X69] :
      ( ( v1_funct_1(k2_partfun1(X66,X67,X68,X69))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( m1_subset_1(k2_partfun1(X66,X67,X68,X69),k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_43,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_relset_1(X47,X48,X49) = k1_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X57,X58,X59] :
      ( ( v1_funct_1(X59)
        | ~ v1_funct_1(X59)
        | ~ v1_partfun1(X59,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( v1_funct_2(X59,X57,X58)
        | ~ v1_funct_1(X59)
        | ~ v1_partfun1(X59,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_47,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk7_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_51,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_52,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | v1_relat_1(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_53,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_54,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | r1_tarski(k7_relat_1(X35,X34),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_55,plain,(
    ! [X44,X45,X46] :
      ( ~ v1_xboole_0(X44)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
      | v1_xboole_0(X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_56,plain,(
    ! [X63,X64,X65] :
      ( ( ~ v1_funct_2(X65,X63,X64)
        | X63 = k1_relset_1(X63,X64,X65)
        | X64 = k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X63 != k1_relset_1(X63,X64,X65)
        | v1_funct_2(X65,X63,X64)
        | X64 = k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( ~ v1_funct_2(X65,X63,X64)
        | X63 = k1_relset_1(X63,X64,X65)
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X63 != k1_relset_1(X63,X64,X65)
        | v1_funct_2(X65,X63,X64)
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( ~ v1_funct_2(X65,X63,X64)
        | X65 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X65 != k1_xboole_0
        | v1_funct_2(X65,X63,X64)
        | X63 = k1_xboole_0
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_57,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( v1_partfun1(esk7_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_31]),c_0_49])])).

cnf(c_0_62,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_64,plain,(
    ! [X70,X71,X72,X73] :
      ( ~ v1_funct_1(X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | k2_partfun1(X70,X71,X72,X73) = k7_relat_1(X72,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_65,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_66,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_67,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_68,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(esk3_0,k2_relat_1(esk7_0),esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(esk7_0,esk3_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_60]),c_0_49])])).

cnf(c_0_73,negated_conjecture,
    ( v4_relat_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( v1_relat_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_63])])).

cnf(c_0_75,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk7_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_36])).

fof(c_0_78,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | k2_relat_1(k7_relat_1(X31,X30)) = k9_relat_1(X31,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_79,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k7_relset_1(X50,X51,X52,X53) = k9_relat_1(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_80,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_81,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_58])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | k1_relat_1(esk7_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_71]),c_0_72])])).

cnf(c_0_84,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_73]),c_0_74])])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(esk3_0,esk6_0,esk7_0,X1) = k7_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_31]),c_0_49])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_88,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_89,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk7_0,X1)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_87]),c_0_36])])).

cnf(c_0_94,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk7_0,X1)) = k9_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_36])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk3_0,esk6_0,esk7_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( k7_relset_1(esk3_0,esk6_0,esk7_0,X1) = k9_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_31])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ r1_tarski(k9_relat_1(esk7_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_92]),c_0_93])]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk7_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_97])).

fof(c_0_102,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | r1_tarski(k1_relat_1(k7_relat_1(X33,X32)),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = esk7_0
    | ~ r1_tarski(esk7_0,k7_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_77])).

cnf(c_0_105,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | v1_funct_2(esk7_0,X1,X2)
    | ~ v1_partfun1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_101]),c_0_49])])).

cnf(c_0_106,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_107,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_108,negated_conjecture,
    ( k1_relset_1(esk3_0,esk5_0,k7_relat_1(esk7_0,esk4_0)) = esk3_0
    | esk5_0 = k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(esk7_0,esk4_0),esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = esk7_0
    | k1_relat_1(esk7_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_97])).

cnf(c_0_110,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | v1_funct_2(esk7_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_60])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk7_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_36])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0))
    | ~ v1_funct_2(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_31]),c_0_49])])).

fof(c_0_114,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(X36,k1_relat_1(X37))
      | k1_relat_1(k7_relat_1(X37,X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_115,negated_conjecture,
    ( k1_relset_1(esk3_0,esk5_0,esk7_0) = esk3_0
    | k1_relat_1(esk7_0) = esk3_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( k1_relset_1(X1,X2,esk7_0) = k1_relat_1(esk7_0)
    | k1_relat_1(esk7_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_101])).

cnf(c_0_117,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_45])).

cnf(c_0_118,negated_conjecture,
    ( k1_relset_1(esk3_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_31])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k9_relat_1(esk7_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_111]),c_0_93])]),c_0_94])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_121,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_122,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_123,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_117])).

cnf(c_0_124,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_84])).

cnf(c_0_125,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_48])]),c_0_118])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_99])).

cnf(c_0_128,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk7_0,esk4_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_86]),c_0_86])).

cnf(c_0_129,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk7_0,X1)) = X1
    | esk5_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_36])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_131,plain,(
    ! [X18] :
      ( ~ r1_tarski(X18,k1_xboole_0)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_132,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_123])).

cnf(c_0_133,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_124])).

cnf(c_0_134,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_45])).

cnf(c_0_135,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk7_0,X1)) = X1
    | esk6_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_125]),c_0_36])])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk7_0,esk4_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_137,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_138,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,k7_relat_1(esk7_0,esk4_0)) = k1_relat_1(k7_relat_1(esk7_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_127])).

cnf(c_0_139,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk7_0,esk4_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_127])])).

cnf(c_0_140,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk7_0,esk4_0)) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_141,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_142,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_132,c_0_84])).

cnf(c_0_143,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_133])).

cnf(c_0_144,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_133])).

cnf(c_0_145,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk7_0,X1),k1_relat_1(k7_relat_1(esk7_0,X1)))) = k1_relat_1(k7_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_93])).

cnf(c_0_146,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk7_0,esk4_0)) = esk4_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_135,c_0_130])).

cnf(c_0_147,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),k7_relat_1(esk7_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_136])).

cnf(c_0_148,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_127])]),c_0_139]),c_0_140])).

cnf(c_0_149,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_150,plain,
    ( r1_tarski(k7_relat_1(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_143])).

cnf(c_0_151,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_144]),c_0_143])])).

cnf(c_0_152,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk7_0,esk4_0),esk4_0)) = esk4_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_153,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148]),c_0_149]),c_0_148]),c_0_149]),c_0_124])])).

cnf(c_0_154,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_150]),c_0_124])])).

cnf(c_0_155,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_141,c_0_151])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk7_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_103])).

cnf(c_0_157,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_152,c_0_153]),c_0_154]),c_0_155])).

cnf(c_0_158,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_159,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k2_zfmisc_1(esk3_0,esk5_0)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk5_0),k7_relat_1(esk7_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_156])).

cnf(c_0_160,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_157]),c_0_84])])).

cnf(c_0_161,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_158])).

cnf(c_0_162,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_133]),c_0_155])).

cnf(c_0_163,negated_conjecture,
    ( k7_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_148]),c_0_149]),c_0_148]),c_0_149]),c_0_124])]),c_0_160])).

cnf(c_0_164,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_133])])).

cnf(c_0_165,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_148]),c_0_160]),c_0_163]),c_0_160]),c_0_164])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.56  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.56  # and selection function SelectNewComplexAHP.
% 0.19/0.56  #
% 0.19/0.56  # Preprocessing time       : 0.029 s
% 0.19/0.56  # Presaturation interreduction done
% 0.19/0.56  
% 0.19/0.56  # Proof found!
% 0.19/0.56  # SZS status Theorem
% 0.19/0.56  # SZS output start CNFRefutation
% 0.19/0.56  fof(t178_funct_2, conjecture, ![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 0.19/0.56  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.56  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.56  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.56  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.56  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.56  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.19/0.56  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.56  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.56  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.56  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.56  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.19/0.56  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.56  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.56  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.56  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.56  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.56  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.56  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.56  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.56  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.56  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.19/0.56  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.56  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.56  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))), inference(assume_negation,[status(cth)],[t178_funct_2])).
% 0.19/0.56  fof(c_0_26, plain, ![X41, X42, X43]:((v4_relat_1(X43,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(v5_relat_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.56  fof(c_0_27, negated_conjecture, (~v1_xboole_0(esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk3_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk6_0))))&((r1_tarski(esk4_0,esk3_0)&r1_tarski(k7_relset_1(esk3_0,esk6_0,esk7_0,esk4_0),esk5_0))&(~v1_funct_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0))|~v1_funct_2(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 0.19/0.56  fof(c_0_28, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.56  fof(c_0_29, plain, ![X26, X27]:((~v4_relat_1(X27,X26)|r1_tarski(k1_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_tarski(k1_relat_1(X27),X26)|v4_relat_1(X27,X26)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.56  cnf(c_0_30, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.56  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_32, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.56  fof(c_0_33, plain, ![X54, X55, X56]:(~v1_relat_1(X56)|(~r1_tarski(k1_relat_1(X56),X54)|~r1_tarski(k2_relat_1(X56),X55)|m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.56  cnf(c_0_34, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_35, negated_conjecture, (v4_relat_1(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.56  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.19/0.56  fof(c_0_37, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.56  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.56  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.56  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.56  fof(c_0_41, plain, ![X60, X61, X62]:((v1_funct_1(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|v1_xboole_0(X61))&(v1_partfun1(X62,X60)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|v1_xboole_0(X61))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.56  fof(c_0_42, plain, ![X66, X67, X68, X69]:((v1_funct_1(k2_partfun1(X66,X67,X68,X69))|(~v1_funct_1(X68)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&(m1_subset_1(k2_partfun1(X66,X67,X68,X69),k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(~v1_funct_1(X68)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.19/0.56  fof(c_0_43, plain, ![X47, X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_relset_1(X47,X48,X49)=k1_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.56  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_36])])).
% 0.19/0.56  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.56  fof(c_0_46, plain, ![X57, X58, X59]:((v1_funct_1(X59)|(~v1_funct_1(X59)|~v1_partfun1(X59,X57))|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(v1_funct_2(X59,X57,X58)|(~v1_funct_1(X59)|~v1_partfun1(X59,X57))|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.56  cnf(c_0_47, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.56  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk7_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_51, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.56  fof(c_0_52, plain, ![X24, X25]:(~v1_relat_1(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|v1_relat_1(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.56  fof(c_0_53, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.56  fof(c_0_54, plain, ![X34, X35]:(~v1_relat_1(X35)|r1_tarski(k7_relat_1(X35,X34),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.19/0.56  fof(c_0_55, plain, ![X44, X45, X46]:(~v1_xboole_0(X44)|(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))|v1_xboole_0(X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.56  fof(c_0_56, plain, ![X63, X64, X65]:((((~v1_funct_2(X65,X63,X64)|X63=k1_relset_1(X63,X64,X65)|X64=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X63!=k1_relset_1(X63,X64,X65)|v1_funct_2(X65,X63,X64)|X64=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))&((~v1_funct_2(X65,X63,X64)|X63=k1_relset_1(X63,X64,X65)|X63!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X63!=k1_relset_1(X63,X64,X65)|v1_funct_2(X65,X63,X64)|X63!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))))&((~v1_funct_2(X65,X63,X64)|X65=k1_xboole_0|X63=k1_xboole_0|X64!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X65!=k1_xboole_0|v1_funct_2(X65,X63,X64)|X63=k1_xboole_0|X64!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.56  cnf(c_0_57, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.56  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(esk7_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.56  cnf(c_0_59, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.56  cnf(c_0_60, negated_conjecture, (v1_partfun1(esk7_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_31]), c_0_48]), c_0_49])]), c_0_50])).
% 0.19/0.56  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_31]), c_0_49])])).
% 0.19/0.56  cnf(c_0_62, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.56  cnf(c_0_63, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.56  fof(c_0_64, plain, ![X70, X71, X72, X73]:(~v1_funct_1(X72)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|k2_partfun1(X70,X71,X72,X73)=k7_relat_1(X72,X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.56  fof(c_0_65, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.56  cnf(c_0_66, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.56  fof(c_0_67, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.56  fof(c_0_68, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.56  cnf(c_0_69, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.56  cnf(c_0_70, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.56  cnf(c_0_71, negated_conjecture, (k1_relset_1(esk3_0,k2_relat_1(esk7_0),esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.56  cnf(c_0_72, negated_conjecture, (v1_funct_2(esk7_0,esk3_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_60]), c_0_49])])).
% 0.19/0.56  cnf(c_0_73, negated_conjecture, (v4_relat_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_61])).
% 0.19/0.56  cnf(c_0_74, negated_conjecture, (v1_relat_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_63])])).
% 0.19/0.56  cnf(c_0_75, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.56  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.56  cnf(c_0_77, negated_conjecture, (r1_tarski(k7_relat_1(esk7_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_36])).
% 0.19/0.56  fof(c_0_78, plain, ![X30, X31]:(~v1_relat_1(X31)|k2_relat_1(k7_relat_1(X31,X30))=k9_relat_1(X31,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.56  fof(c_0_79, plain, ![X50, X51, X52, X53]:(~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|k7_relset_1(X50,X51,X52,X53)=k9_relat_1(X52,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.56  cnf(c_0_80, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.56  cnf(c_0_81, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.56  cnf(c_0_82, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_69, c_0_58])).
% 0.19/0.56  cnf(c_0_83, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|k1_relat_1(esk7_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_58]), c_0_71]), c_0_72])])).
% 0.19/0.56  cnf(c_0_84, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.56  cnf(c_0_85, negated_conjecture, (r1_tarski(k1_relat_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_73]), c_0_74])])).
% 0.19/0.56  cnf(c_0_86, negated_conjecture, (k2_partfun1(esk3_0,esk6_0,esk7_0,X1)=k7_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_31]), c_0_49])])).
% 0.19/0.56  cnf(c_0_87, negated_conjecture, (m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.56  cnf(c_0_88, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.56  cnf(c_0_89, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.56  cnf(c_0_90, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.56  cnf(c_0_91, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.19/0.56  cnf(c_0_92, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk7_0,X1)),esk3_0)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.56  cnf(c_0_93, negated_conjecture, (v1_relat_1(k7_relat_1(esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_87]), c_0_36])])).
% 0.19/0.56  cnf(c_0_94, negated_conjecture, (k2_relat_1(k7_relat_1(esk7_0,X1))=k9_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_36])).
% 0.19/0.56  cnf(c_0_95, negated_conjecture, (r1_tarski(k7_relset_1(esk3_0,esk6_0,esk7_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_96, negated_conjecture, (k7_relset_1(esk3_0,esk6_0,esk7_0,X1)=k9_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_89, c_0_31])).
% 0.19/0.56  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.56  cnf(c_0_98, negated_conjecture, (m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~r1_tarski(k9_relat_1(esk7_0,X1),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_92]), c_0_93])]), c_0_94])).
% 0.19/0.56  cnf(c_0_99, negated_conjecture, (r1_tarski(k9_relat_1(esk7_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 0.19/0.56  cnf(c_0_100, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.56  cnf(c_0_101, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_97])).
% 0.19/0.56  fof(c_0_102, plain, ![X32, X33]:(~v1_relat_1(X33)|r1_tarski(k1_relat_1(k7_relat_1(X33,X32)),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.19/0.56  cnf(c_0_103, negated_conjecture, (m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.56  cnf(c_0_104, negated_conjecture, (k7_relat_1(esk7_0,X1)=esk7_0|~r1_tarski(esk7_0,k7_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_100, c_0_77])).
% 0.19/0.56  cnf(c_0_105, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|v1_funct_2(esk7_0,X1,X2)|~v1_partfun1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_101]), c_0_49])])).
% 0.19/0.56  cnf(c_0_106, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.19/0.56  cnf(c_0_107, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.56  cnf(c_0_108, negated_conjecture, (k1_relset_1(esk3_0,esk5_0,k7_relat_1(esk7_0,esk4_0))=esk3_0|esk5_0=k1_xboole_0|~v1_funct_2(k7_relat_1(esk7_0,esk4_0),esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_103])).
% 0.19/0.56  cnf(c_0_109, negated_conjecture, (k7_relat_1(esk7_0,X1)=esk7_0|k1_relat_1(esk7_0)=esk3_0), inference(spm,[status(thm)],[c_0_104, c_0_97])).
% 0.19/0.56  cnf(c_0_110, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|v1_funct_2(esk7_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_105, c_0_60])).
% 0.19/0.56  cnf(c_0_111, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk7_0,X1)),X1)), inference(spm,[status(thm)],[c_0_106, c_0_36])).
% 0.19/0.56  cnf(c_0_112, negated_conjecture, (~v1_funct_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0))|~v1_funct_2(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_113, negated_conjecture, (v1_funct_1(k2_partfun1(esk3_0,esk6_0,esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_31]), c_0_49])])).
% 0.19/0.56  fof(c_0_114, plain, ![X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(X36,k1_relat_1(X37))|k1_relat_1(k7_relat_1(X37,X36))=X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.56  cnf(c_0_115, negated_conjecture, (k1_relset_1(esk3_0,esk5_0,esk7_0)=esk3_0|k1_relat_1(esk7_0)=esk3_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])).
% 0.19/0.56  cnf(c_0_116, negated_conjecture, (k1_relset_1(X1,X2,esk7_0)=k1_relat_1(esk7_0)|k1_relat_1(esk7_0)=esk3_0), inference(spm,[status(thm)],[c_0_57, c_0_101])).
% 0.19/0.56  cnf(c_0_117, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_45])).
% 0.19/0.56  cnf(c_0_118, negated_conjecture, (k1_relset_1(esk3_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_31])).
% 0.19/0.56  cnf(c_0_119, negated_conjecture, (m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k9_relat_1(esk7_0,X1),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_111]), c_0_93])]), c_0_94])).
% 0.19/0.56  cnf(c_0_120, negated_conjecture, (~v1_funct_2(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 0.19/0.56  cnf(c_0_121, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.19/0.56  cnf(c_0_122, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.19/0.56  cnf(c_0_123, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_69, c_0_117])).
% 0.19/0.56  cnf(c_0_124, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_90, c_0_84])).
% 0.19/0.56  cnf(c_0_125, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_31]), c_0_48])]), c_0_118])).
% 0.19/0.56  cnf(c_0_126, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.56  cnf(c_0_127, negated_conjecture, (m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_119, c_0_99])).
% 0.19/0.56  cnf(c_0_128, negated_conjecture, (~v1_funct_2(k7_relat_1(esk7_0,esk4_0),esk4_0,esk5_0)|~m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_86]), c_0_86])).
% 0.19/0.56  cnf(c_0_129, negated_conjecture, (k1_relat_1(k7_relat_1(esk7_0,X1))=X1|esk5_0=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_36])])).
% 0.19/0.56  cnf(c_0_130, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  fof(c_0_131, plain, ![X18]:(~r1_tarski(X18,k1_xboole_0)|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.56  cnf(c_0_132, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_90, c_0_123])).
% 0.19/0.56  cnf(c_0_133, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_124])).
% 0.19/0.56  cnf(c_0_134, plain, (k1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_45])).
% 0.19/0.56  cnf(c_0_135, negated_conjecture, (k1_relat_1(k7_relat_1(esk7_0,X1))=X1|esk6_0=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_125]), c_0_36])])).
% 0.19/0.56  cnf(c_0_136, negated_conjecture, (r1_tarski(k7_relat_1(esk7_0,esk4_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.19/0.56  cnf(c_0_137, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.56  cnf(c_0_138, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,k7_relat_1(esk7_0,esk4_0))=k1_relat_1(k7_relat_1(esk7_0,esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_127])).
% 0.19/0.56  cnf(c_0_139, negated_conjecture, (~v1_funct_2(k7_relat_1(esk7_0,esk4_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_127])])).
% 0.19/0.56  cnf(c_0_140, negated_conjecture, (k1_relat_1(k7_relat_1(esk7_0,esk4_0))=esk4_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.19/0.56  cnf(c_0_141, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_131])).
% 0.19/0.56  cnf(c_0_142, plain, (r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_132, c_0_84])).
% 0.19/0.56  cnf(c_0_143, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_133])).
% 0.19/0.56  cnf(c_0_144, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_133])).
% 0.19/0.56  cnf(c_0_145, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk7_0,X1),k1_relat_1(k7_relat_1(esk7_0,X1))))=k1_relat_1(k7_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_134, c_0_93])).
% 0.19/0.56  cnf(c_0_146, negated_conjecture, (k1_relat_1(k7_relat_1(esk7_0,esk4_0))=esk4_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_135, c_0_130])).
% 0.19/0.56  cnf(c_0_147, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k2_zfmisc_1(esk4_0,esk5_0)|~r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),k7_relat_1(esk7_0,esk4_0))), inference(spm,[status(thm)],[c_0_100, c_0_136])).
% 0.19/0.56  cnf(c_0_148, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_127])]), c_0_139]), c_0_140])).
% 0.19/0.56  cnf(c_0_149, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_141, c_0_142])).
% 0.19/0.56  cnf(c_0_150, plain, (r1_tarski(k7_relat_1(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_143])).
% 0.19/0.56  cnf(c_0_151, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_144]), c_0_143])])).
% 0.19/0.56  cnf(c_0_152, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk7_0,esk4_0),esk4_0))=esk4_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_145, c_0_146])).
% 0.19/0.56  cnf(c_0_153, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_148]), c_0_149]), c_0_148]), c_0_149]), c_0_124])])).
% 0.19/0.56  cnf(c_0_154, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_150]), c_0_124])])).
% 0.19/0.56  cnf(c_0_155, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_141, c_0_151])).
% 0.19/0.56  cnf(c_0_156, negated_conjecture, (r1_tarski(k7_relat_1(esk7_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_126, c_0_103])).
% 0.19/0.56  cnf(c_0_157, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_152, c_0_153]), c_0_154]), c_0_155])).
% 0.19/0.56  cnf(c_0_158, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.56  cnf(c_0_159, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k2_zfmisc_1(esk3_0,esk5_0)|~r1_tarski(k2_zfmisc_1(esk3_0,esk5_0),k7_relat_1(esk7_0,esk4_0))), inference(spm,[status(thm)],[c_0_100, c_0_156])).
% 0.19/0.56  cnf(c_0_160, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_157]), c_0_84])])).
% 0.19/0.56  cnf(c_0_161, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_158])).
% 0.19/0.56  cnf(c_0_162, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_133]), c_0_155])).
% 0.19/0.56  cnf(c_0_163, negated_conjecture, (k7_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_148]), c_0_149]), c_0_148]), c_0_149]), c_0_124])]), c_0_160])).
% 0.19/0.56  cnf(c_0_164, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_133])])).
% 0.19/0.56  cnf(c_0_165, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_148]), c_0_160]), c_0_163]), c_0_160]), c_0_164])]), ['proof']).
% 0.19/0.56  # SZS output end CNFRefutation
% 0.19/0.56  # Proof object total steps             : 166
% 0.19/0.56  # Proof object clause steps            : 116
% 0.19/0.56  # Proof object formula steps           : 50
% 0.19/0.56  # Proof object conjectures             : 71
% 0.19/0.56  # Proof object clause conjectures      : 68
% 0.19/0.56  # Proof object formula conjectures     : 3
% 0.19/0.56  # Proof object initial clauses used    : 36
% 0.19/0.56  # Proof object initial formulas used   : 25
% 0.19/0.56  # Proof object generating inferences   : 69
% 0.19/0.56  # Proof object simplifying inferences  : 89
% 0.19/0.56  # Training examples: 0 positive, 0 negative
% 0.19/0.56  # Parsed axioms                        : 26
% 0.19/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.56  # Initial clauses                      : 48
% 0.19/0.56  # Removed in clause preprocessing      : 2
% 0.19/0.56  # Initial clauses in saturation        : 46
% 0.19/0.56  # Processed clauses                    : 2929
% 0.19/0.56  # ...of these trivial                  : 32
% 0.19/0.56  # ...subsumed                          : 1946
% 0.19/0.56  # ...remaining for further processing  : 950
% 0.19/0.56  # Other redundant clauses eliminated   : 32
% 0.19/0.56  # Clauses deleted for lack of memory   : 0
% 0.19/0.56  # Backward-subsumed                    : 72
% 0.19/0.56  # Backward-rewritten                   : 547
% 0.19/0.56  # Generated clauses                    : 7956
% 0.19/0.56  # ...of the previous two non-trivial   : 6790
% 0.19/0.56  # Contextual simplify-reflections      : 52
% 0.19/0.56  # Paramodulations                      : 7922
% 0.19/0.56  # Factorizations                       : 3
% 0.19/0.56  # Equation resolutions                 : 32
% 0.19/0.56  # Propositional unsat checks           : 0
% 0.19/0.56  #    Propositional check models        : 0
% 0.19/0.56  #    Propositional check unsatisfiable : 0
% 0.19/0.56  #    Propositional clauses             : 0
% 0.19/0.56  #    Propositional clauses after purity: 0
% 0.19/0.56  #    Propositional unsat core size     : 0
% 0.19/0.56  #    Propositional preprocessing time  : 0.000
% 0.19/0.56  #    Propositional encoding time       : 0.000
% 0.19/0.56  #    Propositional solver time         : 0.000
% 0.19/0.56  #    Success case prop preproc time    : 0.000
% 0.19/0.56  #    Success case prop encoding time   : 0.000
% 0.19/0.56  #    Success case prop solver time     : 0.000
% 0.19/0.56  # Current number of processed clauses  : 280
% 0.19/0.56  #    Positive orientable unit clauses  : 90
% 0.19/0.56  #    Positive unorientable unit clauses: 0
% 0.19/0.56  #    Negative unit clauses             : 3
% 0.19/0.56  #    Non-unit-clauses                  : 187
% 0.19/0.56  # Current number of unprocessed clauses: 3827
% 0.19/0.56  # ...number of literals in the above   : 9905
% 0.19/0.56  # Current number of archived formulas  : 0
% 0.19/0.56  # Current number of archived clauses   : 664
% 0.19/0.56  # Clause-clause subsumption calls (NU) : 63227
% 0.19/0.56  # Rec. Clause-clause subsumption calls : 42653
% 0.19/0.56  # Non-unit clause-clause subsumptions  : 1978
% 0.19/0.56  # Unit Clause-clause subsumption calls : 4538
% 0.19/0.56  # Rewrite failures with RHS unbound    : 0
% 0.19/0.56  # BW rewrite match attempts            : 160
% 0.19/0.56  # BW rewrite match successes           : 27
% 0.19/0.56  # Condensation attempts                : 0
% 0.19/0.56  # Condensation successes               : 0
% 0.19/0.56  # Termbank termtop insertions          : 102008
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.208 s
% 0.39/0.56  # System time              : 0.009 s
% 0.39/0.56  # Total time               : 0.217 s
% 0.39/0.56  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
