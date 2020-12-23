%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 405 expanded)
%              Number of clauses        :   65 ( 160 expanded)
%              Number of leaves         :   20 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  365 (2276 expanded)
%              Number of equality atoms :   78 ( 482 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

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
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k1_relset_1(X54,X55,X56) = k1_relat_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0)
    & v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk8_0,esk9_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
    & v1_funct_1(esk11_0)
    & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0)))
    & m1_subset_1(esk12_0,esk8_0)
    & r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0))
    & esk8_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0) != k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | k2_relset_1(X57,X58,X59) = k2_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X76,X77,X78,X79] :
      ( ( v1_funct_1(X79)
        | X77 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X76,X77,X79),X78)
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X76,X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( v1_funct_2(X79,X76,X78)
        | X77 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X76,X77,X79),X78)
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X76,X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X78)))
        | X77 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X76,X77,X79),X78)
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X76,X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( v1_funct_1(X79)
        | X76 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X76,X77,X79),X78)
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X76,X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( v1_funct_2(X79,X76,X78)
        | X76 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X76,X77,X79),X78)
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X76,X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X78)))
        | X76 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X76,X77,X79),X78)
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X76,X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk9_0,esk7_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(esk8_0,esk9_0,esk10_0) = k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_38,plain,(
    ! [X72,X73,X74,X75] :
      ( ~ v1_funct_1(X75)
      | ~ v1_funct_2(X75,X72,X73)
      | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | ~ r2_hidden(X74,X72)
      | X73 = k1_xboole_0
      | r2_hidden(k1_funct_1(X75,X74),X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_39,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk10_0),k1_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | v1_funct_2(esk10_0,esk8_0,X1)
    | ~ r1_tarski(k2_relat_1(esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_33]),c_0_34]),c_0_32])])).

fof(c_0_42,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk12_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_45,plain,(
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

cnf(c_0_46,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | v1_funct_2(esk10_0,esk8_0,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk12_0,esk8_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_52,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | v1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_56,plain,(
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

fof(c_0_57,plain,(
    ! [X31] :
      ( ~ v1_xboole_0(X31)
      | v1_funct_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_58,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_59,plain,(
    ! [X63,X64,X65] :
      ( ~ v1_relat_1(X64)
      | ~ v5_relat_1(X64,X63)
      | ~ v1_funct_1(X64)
      | ~ r2_hidden(X65,k1_relat_1(X64))
      | k7_partfun1(X63,X64,X65) = k1_funct_1(X64,X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk10_0,X1),k1_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34])]),c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk12_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_62,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_63,plain,(
    ! [X51,X52,X53] :
      ( ( v4_relat_1(X53,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v5_relat_1(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk9_0,esk7_0,X2,esk11_0),X3) = k1_funct_1(esk11_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk9_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk9_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk9_0,X2),k1_relat_1(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_54]),c_0_30])]),c_0_55])).

fof(c_0_65,plain,(
    ! [X22,X23] :
      ( ( k2_zfmisc_1(X22,X23) != k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_66,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk10_0,esk12_0),k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_73,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),X1) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,X1))
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_34]),c_0_28]),c_0_32]),c_0_40])]),c_0_51])).

fof(c_0_75,plain,(
    ! [X24,X25] : ~ r2_hidden(X24,k2_zfmisc_1(X24,X25)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_77,plain,(
    ! [X20,X21] :
      ( v1_xboole_0(X21)
      | ~ r1_tarski(X21,X20)
      | ~ r1_xboole_0(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_79,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_xboole_0(X12,X13) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r1_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_61])).

cnf(c_0_82,negated_conjecture,
    ( k7_partfun1(X1,esk11_0,k1_funct_1(esk10_0,esk12_0)) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))
    | k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | ~ v5_relat_1(esk11_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_54]),c_0_72])])).

cnf(c_0_83,negated_conjecture,
    ( v5_relat_1(esk11_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_25])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0) != k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_44])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_28])).

cnf(c_0_90,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_47])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_xboole_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_28]),c_0_33])]),c_0_55]),c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))
    | k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) != k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(esk10_0)
    | ~ r1_xboole_0(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | ~ r1_xboole_0(esk10_0,k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_91]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_87]),c_0_100])])).

cnf(c_0_103,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_87]),c_0_103])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:35:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.19/0.47  # and selection function SelectNewComplexAHP.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.031 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.19/0.47  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.47  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.47  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 0.19/0.47  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.47  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.19/0.47  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.47  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.19/0.47  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.47  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.19/0.47  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.19/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.47  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.19/0.47  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.47  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.47  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.47  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.19/0.47  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.47  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.19/0.47  fof(c_0_21, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|k1_relset_1(X54,X55,X56)=k1_relat_1(X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.47  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk9_0)&(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk8_0,esk9_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&((v1_funct_1(esk11_0)&m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0))))&(m1_subset_1(esk12_0,esk8_0)&(r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0))&(esk8_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0)!=k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.19/0.47  fof(c_0_23, plain, ![X57, X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|k2_relset_1(X57,X58,X59)=k2_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.47  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  fof(c_0_26, plain, ![X76, X77, X78, X79]:((((v1_funct_1(X79)|X77=k1_xboole_0|~r1_tarski(k2_relset_1(X76,X77,X79),X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))))&(v1_funct_2(X79,X76,X78)|X77=k1_xboole_0|~r1_tarski(k2_relset_1(X76,X77,X79),X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))))&(m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X78)))|X77=k1_xboole_0|~r1_tarski(k2_relset_1(X76,X77,X79),X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))))&(((v1_funct_1(X79)|X76!=k1_xboole_0|~r1_tarski(k2_relset_1(X76,X77,X79),X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))))&(v1_funct_2(X79,X76,X78)|X76!=k1_xboole_0|~r1_tarski(k2_relset_1(X76,X77,X79),X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))))&(m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X78)))|X76!=k1_xboole_0|~r1_tarski(k2_relset_1(X76,X77,X79),X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X76,X77)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.19/0.47  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk9_0,esk7_0,esk11_0)=k1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.47  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (k2_relset_1(esk8_0,esk9_0,esk10_0)=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relat_1(esk11_0))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.47  cnf(c_0_36, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  fof(c_0_37, plain, ![X26, X27]:(~m1_subset_1(X26,X27)|(v1_xboole_0(X27)|r2_hidden(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.47  fof(c_0_38, plain, ![X72, X73, X74, X75]:(~v1_funct_1(X75)|~v1_funct_2(X75,X72,X73)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))|(~r2_hidden(X74,X72)|(X73=k1_xboole_0|r2_hidden(k1_funct_1(X75,X74),X73)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.19/0.47  cnf(c_0_39, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))|~r1_tarski(k2_relat_1(esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_28])])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relat_1(esk10_0),k1_relat_1(esk11_0))), inference(rw,[status(thm)],[c_0_35, c_0_32])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (esk9_0=k1_xboole_0|v1_funct_2(esk10_0,esk8_0,X1)|~r1_tarski(k2_relat_1(esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_33]), c_0_34]), c_0_32])])).
% 0.19/0.47  fof(c_0_42, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.47  cnf(c_0_43, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk12_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  fof(c_0_45, plain, ![X66, X67, X68, X69, X70, X71]:(v1_xboole_0(X68)|(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|(~v1_funct_1(X70)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X66)))|(~m1_subset_1(X71,X67)|(~r1_tarski(k2_relset_1(X67,X68,X69),k1_relset_1(X68,X66,X70))|(X67=k1_xboole_0|k1_funct_1(k8_funct_2(X67,X68,X66,X69,X70),X71)=k1_funct_1(X70,k1_funct_1(X69,X71)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.19/0.47  cnf(c_0_46, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.47  cnf(c_0_48, negated_conjecture, (esk9_0=k1_xboole_0|v1_funct_2(esk10_0,esk8_0,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.19/0.47  cnf(c_0_49, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (r2_hidden(esk12_0,esk8_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  fof(c_0_52, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|v1_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.47  cnf(c_0_53, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.47  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  fof(c_0_56, plain, ![X60, X61, X62]:(((v1_funct_1(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61)))&(~v1_xboole_0(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61))))&(v1_funct_2(X62,X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.19/0.47  fof(c_0_57, plain, ![X31]:(~v1_xboole_0(X31)|v1_funct_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.19/0.47  fof(c_0_58, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_59, plain, ![X63, X64, X65]:(~v1_relat_1(X64)|~v5_relat_1(X64,X63)|~v1_funct_1(X64)|(~r2_hidden(X65,k1_relat_1(X64))|k7_partfun1(X63,X64,X65)=k1_funct_1(X64,X65))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0|r2_hidden(k1_funct_1(esk10_0,X1),k1_relat_1(esk11_0))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_34])]), c_0_48])).
% 0.19/0.47  cnf(c_0_61, negated_conjecture, (r2_hidden(esk12_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.47  cnf(c_0_62, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.47  fof(c_0_63, plain, ![X51, X52, X53]:((v4_relat_1(X53,X51)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(v5_relat_1(X53,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk9_0,esk7_0,X2,esk11_0),X3)=k1_funct_1(esk11_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk9_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk9_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk9_0,X2),k1_relat_1(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_54]), c_0_30])]), c_0_55])).
% 0.19/0.47  fof(c_0_65, plain, ![X22, X23]:((k2_zfmisc_1(X22,X23)!=k1_xboole_0|(X22=k1_xboole_0|X23=k1_xboole_0))&((X22!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0)&(X23!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.47  fof(c_0_66, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.47  cnf(c_0_67, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.47  cnf(c_0_68, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.47  cnf(c_0_69, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.47  cnf(c_0_70, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0|r2_hidden(k1_funct_1(esk10_0,esk12_0),k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_62, c_0_25])).
% 0.19/0.47  cnf(c_0_73, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),X1)=k1_funct_1(esk11_0,k1_funct_1(esk10_0,X1))|~m1_subset_1(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_33]), c_0_34]), c_0_28]), c_0_32]), c_0_40])]), c_0_51])).
% 0.19/0.47  fof(c_0_75, plain, ![X24, X25]:~r2_hidden(X24,k2_zfmisc_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.47  cnf(c_0_76, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.47  fof(c_0_77, plain, ![X20, X21]:(v1_xboole_0(X21)|(~r1_tarski(X21,X20)|~r1_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.19/0.47  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.47  fof(c_0_79, plain, ![X12, X13, X15, X16, X17]:(((r2_hidden(esk2_2(X12,X13),X12)|r1_xboole_0(X12,X13))&(r2_hidden(esk2_2(X12,X13),X13)|r1_xboole_0(X12,X13)))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|~r1_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.47  cnf(c_0_80, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_69, c_0_61])).
% 0.19/0.47  cnf(c_0_82, negated_conjecture, (k7_partfun1(X1,esk11_0,k1_funct_1(esk10_0,esk12_0))=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))|k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0|~v5_relat_1(esk11_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_54]), c_0_72])])).
% 0.19/0.47  cnf(c_0_83, negated_conjecture, (v5_relat_1(esk11_0,esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_25])).
% 0.19/0.47  cnf(c_0_84, negated_conjecture, (k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0)!=k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_85, negated_conjecture, (k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0)=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))), inference(spm,[status(thm)],[c_0_74, c_0_44])).
% 0.19/0.47  cnf(c_0_86, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.47  cnf(c_0_87, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_76])).
% 0.19/0.47  cnf(c_0_88, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.47  cnf(c_0_89, negated_conjecture, (r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_78, c_0_28])).
% 0.19/0.47  cnf(c_0_90, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.47  cnf(c_0_91, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)))), inference(spm,[status(thm)],[c_0_78, c_0_47])).
% 0.19/0.47  cnf(c_0_92, negated_conjecture, (~v1_xboole_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_28]), c_0_33])]), c_0_55]), c_0_81])).
% 0.19/0.47  cnf(c_0_93, negated_conjecture, (k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0))=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))|k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.47  cnf(c_0_94, negated_conjecture, (k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0))!=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.47  cnf(c_0_95, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.47  cnf(c_0_96, negated_conjecture, (v1_xboole_0(esk10_0)|~r1_xboole_0(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.47  cnf(c_0_97, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_69, c_0_90])).
% 0.19/0.47  cnf(c_0_98, negated_conjecture, (esk9_0=k1_xboole_0|~r1_xboole_0(esk10_0,k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_91]), c_0_92])).
% 0.19/0.47  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.47  cnf(c_0_100, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_95, c_0_90])).
% 0.19/0.47  cnf(c_0_101, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_92])).
% 0.19/0.47  cnf(c_0_102, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_87]), c_0_100])])).
% 0.19/0.47  cnf(c_0_103, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.47  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_87]), c_0_103])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 105
% 0.19/0.47  # Proof object clause steps            : 65
% 0.19/0.47  # Proof object formula steps           : 40
% 0.19/0.47  # Proof object conjectures             : 43
% 0.19/0.47  # Proof object clause conjectures      : 40
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 30
% 0.19/0.47  # Proof object initial formulas used   : 20
% 0.19/0.47  # Proof object generating inferences   : 29
% 0.19/0.47  # Proof object simplifying inferences  : 43
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 25
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 61
% 0.19/0.47  # Removed in clause preprocessing      : 4
% 0.19/0.47  # Initial clauses in saturation        : 57
% 0.19/0.47  # Processed clauses                    : 919
% 0.19/0.47  # ...of these trivial                  : 2
% 0.19/0.47  # ...subsumed                          : 388
% 0.19/0.47  # ...remaining for further processing  : 529
% 0.19/0.47  # Other redundant clauses eliminated   : 22
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 63
% 0.19/0.47  # Backward-rewritten                   : 201
% 0.19/0.47  # Generated clauses                    : 3496
% 0.19/0.47  # ...of the previous two non-trivial   : 3320
% 0.19/0.47  # Contextual simplify-reflections      : 13
% 0.19/0.47  # Paramodulations                      : 3458
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 37
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 206
% 0.19/0.47  #    Positive orientable unit clauses  : 46
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 15
% 0.19/0.47  #    Non-unit-clauses                  : 145
% 0.19/0.47  # Current number of unprocessed clauses: 2472
% 0.19/0.47  # ...number of literals in the above   : 11997
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 321
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 23840
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 7109
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 365
% 0.19/0.47  # Unit Clause-clause subsumption calls : 2487
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 81
% 0.19/0.47  # BW rewrite match successes           : 20
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 57360
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.129 s
% 0.19/0.47  # System time              : 0.006 s
% 0.19/0.47  # Total time               : 0.135 s
% 0.19/0.47  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
