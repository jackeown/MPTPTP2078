%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:56 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 309 expanded)
%              Number of clauses        :   61 ( 120 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  331 (1653 expanded)
%              Number of equality atoms :   87 ( 366 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d12_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( r1_tarski(k2_relset_1(X1,X2,X4),k1_relset_1(X2,X3,X5))
           => ( X2 = k1_xboole_0
              | k8_funct_2(X1,X2,X3,X4,X5) = k1_partfun1(X1,X2,X2,X3,X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

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

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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
    ! [X50,X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k1_relset_1(X50,X51,X52) = k1_relat_1(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))
    & m1_subset_1(esk8_0,esk4_0)
    & r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))
    & esk4_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) != k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X61,X62,X63] :
      ( ( ~ v1_funct_2(X63,X61,X62)
        | X61 = k1_relset_1(X61,X62,X63)
        | X62 = k1_xboole_0
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( X61 != k1_relset_1(X61,X62,X63)
        | v1_funct_2(X63,X61,X62)
        | X62 = k1_xboole_0
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( ~ v1_funct_2(X63,X61,X62)
        | X61 = k1_relset_1(X61,X62,X63)
        | X61 != k1_xboole_0
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( X61 != k1_relset_1(X61,X62,X63)
        | v1_funct_2(X63,X61,X62)
        | X61 != k1_xboole_0
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( ~ v1_funct_2(X63,X61,X62)
        | X63 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 != k1_xboole_0
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( X63 != k1_xboole_0
        | v1_funct_2(X63,X61,X62)
        | X61 = k1_xboole_0
        | X62 != k1_xboole_0
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | v1_relat_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_27,plain,(
    ! [X34,X35] : v1_relat_1(k2_zfmisc_1(X34,X35)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X53,X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | k2_relset_1(X53,X54,X55) = k2_relat_1(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_31,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v5_relat_1(X37,X36)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X38,k1_relat_1(X37))
      | r2_hidden(k1_funct_1(X37,X38),X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_32,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X31,X32] :
      ( ( ~ v5_relat_1(X32,X31)
        | r1_tarski(k2_relat_1(X32),X31)
        | ~ v1_relat_1(X32) )
      & ( ~ r1_tarski(k2_relat_1(X32),X31)
        | v5_relat_1(X32,X31)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( k1_relset_1(esk5_0,esk3_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_29])).

cnf(c_0_42,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_33]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_36])])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_52,plain,(
    ! [X67,X68,X69,X70,X71,X72] :
      ( ~ v1_funct_1(X71)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | ~ v1_funct_1(X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | k1_partfun1(X67,X68,X69,X70,X71,X72) = k5_relat_1(X71,X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_53,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),X2)
    | ~ v5_relat_1(esk6_0,X2)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_57,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_61,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( ~ v1_funct_1(X59)
      | ~ v1_funct_2(X59,X56,X57)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | ~ r1_tarski(k2_relset_1(X56,X57,X59),k1_relset_1(X57,X58,X60))
      | X57 = k1_xboole_0
      | k8_funct_2(X56,X57,X58,X59,X60) = k1_partfun1(X56,X57,X57,X58,X59,X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_2])])])).

cnf(c_0_62,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_46])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_68,plain,
    ( X3 = k1_xboole_0
    | k8_funct_2(X2,X3,X5,X1,X4) = k1_partfun1(X2,X3,X3,X5,X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X2,X3,X1),k1_relset_1(X3,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k1_partfun1(X1,X2,esk5_0,esk3_0,X3,esk7_0) = k5_relat_1(X3,esk7_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_63])])).

fof(c_0_70,plain,(
    ! [X64,X65,X66] :
      ( ~ v1_relat_1(X65)
      | ~ v5_relat_1(X65,X64)
      | ~ v1_funct_1(X65)
      | ~ r2_hidden(X66,k1_relat_1(X65))
      | k7_partfun1(X64,X65,X66) = k1_funct_1(X65,X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk8_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_73,plain,(
    ! [X44,X45,X46] :
      ( ( v4_relat_1(X46,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v5_relat_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_74,negated_conjecture,
    ( k1_partfun1(X1,esk5_0,esk5_0,esk3_0,X2,esk7_0) = k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0)
    | esk5_0 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk5_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_29]),c_0_63]),c_0_41])])).

cnf(c_0_75,negated_conjecture,
    ( k1_partfun1(esk4_0,esk5_0,esk5_0,esk3_0,esk6_0,esk7_0) = k5_relat_1(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_25]),c_0_45])])).

cnf(c_0_76,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk8_0),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_36])])).

cnf(c_0_79,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_80,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | ~ r2_hidden(X39,k1_relat_1(X40))
      | k1_funct_1(k5_relat_1(X40,X41),X39) = k1_funct_1(X41,k1_funct_1(X40,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) != k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0) = k5_relat_1(esk6_0,esk7_0)
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_34]),c_0_75]),c_0_45]),c_0_25]),c_0_55]),c_0_65])])).

cnf(c_0_83,negated_conjecture,
    ( k7_partfun1(X1,esk7_0,k1_funct_1(esk6_0,esk8_0)) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))
    | esk5_0 = k1_xboole_0
    | ~ v5_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_63]),c_0_78])])).

cnf(c_0_84,negated_conjecture,
    ( v5_relat_1(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_29])).

cnf(c_0_85,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_86,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_87,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) != k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,X1),X2) = k1_funct_1(X1,k1_funct_1(esk6_0,X2))
    | esk5_0 = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_93,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk8_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,X1),esk8_0) = k1_funct_1(X1,k1_funct_1(esk6_0,esk8_0))
    | esk5_0 = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_67])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_99,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_63]),c_0_78])])).

cnf(c_0_100,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.90/1.07  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.90/1.07  # and selection function SelectNewComplexAHP.
% 0.90/1.07  #
% 0.90/1.07  # Preprocessing time       : 0.029 s
% 0.90/1.07  # Presaturation interreduction done
% 0.90/1.07  
% 0.90/1.07  # Proof found!
% 0.90/1.07  # SZS status Theorem
% 0.90/1.07  # SZS output start CNFRefutation
% 0.90/1.07  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.90/1.07  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.90/1.07  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.90/1.07  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.90/1.07  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.90/1.07  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.90/1.07  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.90/1.07  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 0.90/1.07  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.90/1.07  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.90/1.07  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.90/1.07  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.90/1.07  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.90/1.07  fof(d12_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(r1_tarski(k2_relset_1(X1,X2,X4),k1_relset_1(X2,X3,X5))=>(X2=k1_xboole_0|k8_funct_2(X1,X2,X3,X4,X5)=k1_partfun1(X1,X2,X2,X3,X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 0.90/1.07  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.90/1.07  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.90/1.07  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.90/1.07  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.90/1.07  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.90/1.07  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.90/1.07  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.90/1.07  fof(c_0_21, plain, ![X50, X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|k1_relset_1(X50,X51,X52)=k1_relat_1(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.90/1.07  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(m1_subset_1(esk8_0,esk4_0)&(r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))&(esk4_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)!=k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.90/1.07  fof(c_0_23, plain, ![X61, X62, X63]:((((~v1_funct_2(X63,X61,X62)|X61=k1_relset_1(X61,X62,X63)|X62=k1_xboole_0|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))&(X61!=k1_relset_1(X61,X62,X63)|v1_funct_2(X63,X61,X62)|X62=k1_xboole_0|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))&((~v1_funct_2(X63,X61,X62)|X61=k1_relset_1(X61,X62,X63)|X61!=k1_xboole_0|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))&(X61!=k1_relset_1(X61,X62,X63)|v1_funct_2(X63,X61,X62)|X61!=k1_xboole_0|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))))&((~v1_funct_2(X63,X61,X62)|X63=k1_xboole_0|X61=k1_xboole_0|X62!=k1_xboole_0|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))&(X63!=k1_xboole_0|v1_funct_2(X63,X61,X62)|X61=k1_xboole_0|X62!=k1_xboole_0|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.90/1.07  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.90/1.07  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  fof(c_0_26, plain, ![X27, X28]:(~v1_relat_1(X27)|(~m1_subset_1(X28,k1_zfmisc_1(X27))|v1_relat_1(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.90/1.07  fof(c_0_27, plain, ![X34, X35]:v1_relat_1(k2_zfmisc_1(X34,X35)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.90/1.07  fof(c_0_28, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.90/1.07  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  fof(c_0_30, plain, ![X53, X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|k2_relset_1(X53,X54,X55)=k2_relat_1(X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.90/1.07  fof(c_0_31, plain, ![X36, X37, X38]:(~v1_relat_1(X37)|~v5_relat_1(X37,X36)|~v1_funct_1(X37)|(~r2_hidden(X38,k1_relat_1(X37))|r2_hidden(k1_funct_1(X37,X38),X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.90/1.07  cnf(c_0_32, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.90/1.07  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.90/1.07  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_35, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.90/1.07  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.90/1.07  fof(c_0_37, plain, ![X31, X32]:((~v5_relat_1(X32,X31)|r1_tarski(k2_relat_1(X32),X31)|~v1_relat_1(X32))&(~r1_tarski(k2_relat_1(X32),X31)|v5_relat_1(X32,X31)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.90/1.07  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.90/1.07  fof(c_0_39, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.90/1.07  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_41, negated_conjecture, (k1_relset_1(esk5_0,esk3_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_29])).
% 0.90/1.07  cnf(c_0_42, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.90/1.07  cnf(c_0_43, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.90/1.07  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_33]), c_0_34])])).
% 0.90/1.07  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_36])])).
% 0.90/1.07  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.90/1.07  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.90/1.07  fof(c_0_49, plain, ![X17]:(~v1_xboole_0(X17)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.90/1.07  cnf(c_0_50, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.90/1.07  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  fof(c_0_52, plain, ![X67, X68, X69, X70, X71, X72]:(~v1_funct_1(X71)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|~v1_funct_1(X72)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|k1_partfun1(X67,X68,X69,X70,X71,X72)=k5_relat_1(X71,X72)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.90/1.07  fof(c_0_53, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.90/1.07  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.90/1.07  cnf(c_0_55, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.90/1.07  cnf(c_0_56, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),X2)|~v5_relat_1(esk6_0,X2)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.90/1.07  cnf(c_0_57, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.90/1.07  cnf(c_0_58, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.90/1.07  cnf(c_0_59, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.90/1.07  cnf(c_0_60, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  fof(c_0_61, plain, ![X56, X57, X58, X59, X60]:(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|(~v1_funct_1(X60)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|(~r1_tarski(k2_relset_1(X56,X57,X59),k1_relset_1(X57,X58,X60))|(X57=k1_xboole_0|k8_funct_2(X56,X57,X58,X59,X60)=k1_partfun1(X56,X57,X57,X58,X59,X60))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_2])])])).
% 0.90/1.07  cnf(c_0_62, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.90/1.07  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.90/1.07  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.90/1.07  cnf(c_0_66, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_46])])).
% 0.90/1.07  cnf(c_0_67, negated_conjecture, (r2_hidden(esk8_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.90/1.07  cnf(c_0_68, plain, (X3=k1_xboole_0|k8_funct_2(X2,X3,X5,X1,X4)=k1_partfun1(X2,X3,X3,X5,X1,X4)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))|~r1_tarski(k2_relset_1(X2,X3,X1),k1_relset_1(X3,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.90/1.07  cnf(c_0_69, negated_conjecture, (k1_partfun1(X1,X2,esk5_0,esk3_0,X3,esk7_0)=k5_relat_1(X3,esk7_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_29]), c_0_63])])).
% 0.90/1.07  fof(c_0_70, plain, ![X64, X65, X66]:(~v1_relat_1(X65)|~v5_relat_1(X65,X64)|~v1_funct_1(X65)|(~r2_hidden(X66,k1_relat_1(X65))|k7_partfun1(X64,X65,X66)=k1_funct_1(X65,X66))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.90/1.07  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.90/1.07  cnf(c_0_72, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk8_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.90/1.07  fof(c_0_73, plain, ![X44, X45, X46]:((v4_relat_1(X46,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(v5_relat_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.90/1.07  cnf(c_0_74, negated_conjecture, (k1_partfun1(X1,esk5_0,esk5_0,esk3_0,X2,esk7_0)=k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0)|esk5_0=k1_xboole_0|~v1_funct_2(X2,X1,esk5_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_29]), c_0_63]), c_0_41])])).
% 0.90/1.07  cnf(c_0_75, negated_conjecture, (k1_partfun1(esk4_0,esk5_0,esk5_0,esk3_0,esk6_0,esk7_0)=k5_relat_1(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_25]), c_0_45])])).
% 0.90/1.07  cnf(c_0_76, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.90/1.07  cnf(c_0_77, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk8_0),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.90/1.07  cnf(c_0_78, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_36])])).
% 0.90/1.07  cnf(c_0_79, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.90/1.07  fof(c_0_80, plain, ![X39, X40, X41]:(~v1_relat_1(X40)|~v1_funct_1(X40)|(~v1_relat_1(X41)|~v1_funct_1(X41)|(~r2_hidden(X39,k1_relat_1(X40))|k1_funct_1(k5_relat_1(X40,X41),X39)=k1_funct_1(X41,k1_funct_1(X40,X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.90/1.07  cnf(c_0_81, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)!=k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_82, negated_conjecture, (k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0)=k5_relat_1(esk6_0,esk7_0)|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_34]), c_0_75]), c_0_45]), c_0_25]), c_0_55]), c_0_65])])).
% 0.90/1.07  cnf(c_0_83, negated_conjecture, (k7_partfun1(X1,esk7_0,k1_funct_1(esk6_0,esk8_0))=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))|esk5_0=k1_xboole_0|~v5_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_63]), c_0_78])])).
% 0.90/1.07  cnf(c_0_84, negated_conjecture, (v5_relat_1(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_79, c_0_29])).
% 0.90/1.07  cnf(c_0_85, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.90/1.07  fof(c_0_86, plain, ![X42, X43]:(~r2_hidden(X42,X43)|~r1_tarski(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.90/1.07  fof(c_0_87, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.90/1.07  cnf(c_0_88, negated_conjecture, (esk5_0=k1_xboole_0|k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))!=k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.90/1.07  cnf(c_0_89, negated_conjecture, (k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.90/1.07  cnf(c_0_90, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,X1),X2)=k1_funct_1(X1,k1_funct_1(esk6_0,X2))|esk5_0=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_44]), c_0_45]), c_0_46])])).
% 0.90/1.07  cnf(c_0_91, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.90/1.07  cnf(c_0_92, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.90/1.07  fof(c_0_93, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.90/1.07  cnf(c_0_94, negated_conjecture, (esk5_0=k1_xboole_0|k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk8_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.90/1.07  cnf(c_0_95, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,X1),esk8_0)=k1_funct_1(X1,k1_funct_1(esk6_0,esk8_0))|esk5_0=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_90, c_0_67])).
% 0.90/1.07  cnf(c_0_96, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.90/1.07  cnf(c_0_97, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.90/1.07  cnf(c_0_98, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_99, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_63]), c_0_78])])).
% 0.90/1.07  cnf(c_0_100, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.90/1.07  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99]), c_0_100])]), ['proof']).
% 0.90/1.07  # SZS output end CNFRefutation
% 0.90/1.07  # Proof object total steps             : 102
% 0.90/1.07  # Proof object clause steps            : 61
% 0.90/1.07  # Proof object formula steps           : 41
% 0.90/1.07  # Proof object conjectures             : 41
% 0.90/1.07  # Proof object clause conjectures      : 38
% 0.90/1.07  # Proof object formula conjectures     : 3
% 0.90/1.07  # Proof object initial clauses used    : 29
% 0.90/1.07  # Proof object initial formulas used   : 20
% 0.90/1.07  # Proof object generating inferences   : 28
% 0.90/1.07  # Proof object simplifying inferences  : 41
% 0.90/1.07  # Training examples: 0 positive, 0 negative
% 0.90/1.07  # Parsed axioms                        : 25
% 0.90/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.90/1.07  # Initial clauses                      : 50
% 0.90/1.07  # Removed in clause preprocessing      : 0
% 0.90/1.07  # Initial clauses in saturation        : 50
% 0.90/1.07  # Processed clauses                    : 10253
% 0.90/1.07  # ...of these trivial                  : 3
% 0.90/1.07  # ...subsumed                          : 8550
% 0.90/1.07  # ...remaining for further processing  : 1700
% 0.90/1.07  # Other redundant clauses eliminated   : 11
% 0.90/1.07  # Clauses deleted for lack of memory   : 0
% 0.90/1.07  # Backward-subsumed                    : 217
% 0.90/1.07  # Backward-rewritten                   : 956
% 0.90/1.07  # Generated clauses                    : 41992
% 0.90/1.07  # ...of the previous two non-trivial   : 38605
% 0.90/1.07  # Contextual simplify-reflections      : 110
% 0.90/1.07  # Paramodulations                      : 41950
% 0.90/1.07  # Factorizations                       : 18
% 0.90/1.07  # Equation resolutions                 : 24
% 0.90/1.07  # Propositional unsat checks           : 0
% 0.90/1.07  #    Propositional check models        : 0
% 0.90/1.07  #    Propositional check unsatisfiable : 0
% 0.90/1.07  #    Propositional clauses             : 0
% 0.90/1.07  #    Propositional clauses after purity: 0
% 0.90/1.07  #    Propositional unsat core size     : 0
% 0.90/1.07  #    Propositional preprocessing time  : 0.000
% 0.90/1.07  #    Propositional encoding time       : 0.000
% 0.90/1.07  #    Propositional solver time         : 0.000
% 0.90/1.07  #    Success case prop preproc time    : 0.000
% 0.90/1.07  #    Success case prop encoding time   : 0.000
% 0.90/1.07  #    Success case prop solver time     : 0.000
% 0.90/1.07  # Current number of processed clauses  : 476
% 0.90/1.07  #    Positive orientable unit clauses  : 38
% 0.90/1.07  #    Positive unorientable unit clauses: 0
% 0.90/1.07  #    Negative unit clauses             : 9
% 0.90/1.07  #    Non-unit-clauses                  : 429
% 0.90/1.07  # Current number of unprocessed clauses: 27638
% 0.90/1.07  # ...number of literals in the above   : 141735
% 0.90/1.07  # Current number of archived formulas  : 0
% 0.90/1.07  # Current number of archived clauses   : 1222
% 0.90/1.07  # Clause-clause subsumption calls (NU) : 1113234
% 0.90/1.07  # Rec. Clause-clause subsumption calls : 249616
% 0.90/1.07  # Non-unit clause-clause subsumptions  : 8457
% 0.90/1.07  # Unit Clause-clause subsumption calls : 2228
% 0.90/1.07  # Rewrite failures with RHS unbound    : 0
% 0.90/1.07  # BW rewrite match attempts            : 50
% 0.90/1.07  # BW rewrite match successes           : 8
% 0.90/1.07  # Condensation attempts                : 0
% 0.90/1.07  # Condensation successes               : 0
% 0.90/1.07  # Termbank termtop insertions          : 651428
% 0.90/1.07  
% 0.90/1.07  # -------------------------------------------------
% 0.90/1.07  # User time                : 0.709 s
% 0.90/1.07  # System time              : 0.016 s
% 0.90/1.07  # Total time               : 0.725 s
% 0.90/1.07  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
