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
% DateTime   : Thu Dec  3 11:07:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 282 expanded)
%              Number of clauses        :   65 ( 116 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  380 (1646 expanded)
%              Number of equality atoms :   86 ( 333 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X51,X52,X53,X54] :
      ( ( v1_funct_1(X54)
        | X52 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X51,X52,X54),X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v1_funct_2(X54,X51,X53)
        | X52 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X51,X52,X54),X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X53)))
        | X52 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X51,X52,X54),X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v1_funct_1(X54)
        | X51 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X51,X52,X54),X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v1_funct_2(X54,X51,X53)
        | X51 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X51,X52,X54),X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X53)))
        | X51 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X51,X52,X54),X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_22,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( v1_xboole_0(X43)
      | ~ v1_funct_1(X44)
      | ~ v1_funct_2(X44,X42,X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | ~ v1_funct_1(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X41)))
      | ~ m1_subset_1(X46,X42)
      | ~ r1_tarski(k2_relset_1(X42,X43,X44),k1_relset_1(X43,X41,X45))
      | X42 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X42,X43,X41,X44,X45),X46) = k1_funct_1(X45,k1_funct_1(X44,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_23,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X47,X48)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ r2_hidden(X49,X47)
      | X48 = k1_xboole_0
      | r2_hidden(k1_funct_1(X50,X49),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k2_relset_1(X3,X1,X2))))
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(esk6_0,esk4_0,X1)
    | ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

fof(c_0_38,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0),X3) = k1_funct_1(esk7_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk5_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k1_relset_1(esk5_0,esk3_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

fof(c_0_41,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relset_1(esk4_0,esk5_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(esk6_0,esk4_0,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0),X3) = k1_funct_1(esk7_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk5_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),k2_relset_1(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29])]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_54,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_28]),c_0_29]),c_0_27])]),c_0_49])).

fof(c_0_56,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_57,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v5_relat_1(X39,X38)
      | ~ v1_funct_1(X39)
      | ~ r2_hidden(X40,k1_relat_1(X39))
      | k7_partfun1(X38,X39,X40) = k1_funct_1(X39,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk8_0),k2_relset_1(esk4_0,esk5_0,esk6_0))
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_61,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_51])])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_65,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk8_0),k1_relat_1(esk7_0))
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_31])).

cnf(c_0_68,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) != k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_47])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_73,negated_conjecture,
    ( k7_partfun1(X1,esk7_0,k1_funct_1(esk6_0,esk8_0)) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))
    | k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk4_0)
    | ~ v5_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_32])])).

cnf(c_0_74,negated_conjecture,
    ( v5_relat_1(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_76,plain,(
    ! [X35,X36,X37] :
      ( ( v1_funct_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) )
      & ( ~ v1_xboole_0(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) )
      & ( v1_funct_2(X37,X35,X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_77,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(X25)
      | v1_funct_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_78,plain,(
    ! [X21,X22] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_xboole_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

fof(c_0_82,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_81])).

cnf(c_0_88,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,k2_relset_1(esk4_0,esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_44])).

cnf(c_0_91,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_49])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_28])]),c_0_33])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_72])])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_96]),c_0_49])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_97]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:47:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.43  # and selection function SelectNewComplexAHP.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.047 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.20/0.43  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 0.20/0.43  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.20/0.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.43  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.20/0.43  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.20/0.43  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.43  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.20/0.43  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.20/0.43  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.43  fof(c_0_17, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.20/0.43  fof(c_0_19, plain, ![X51, X52, X53, X54]:((((v1_funct_1(X54)|X52=k1_xboole_0|~r1_tarski(k2_relset_1(X51,X52,X54),X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v1_funct_2(X54,X51,X53)|X52=k1_xboole_0|~r1_tarski(k2_relset_1(X51,X52,X54),X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&(m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X53)))|X52=k1_xboole_0|~r1_tarski(k2_relset_1(X51,X52,X54),X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&(((v1_funct_1(X54)|X51!=k1_xboole_0|~r1_tarski(k2_relset_1(X51,X52,X54),X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v1_funct_2(X54,X51,X53)|X51!=k1_xboole_0|~r1_tarski(k2_relset_1(X51,X52,X54),X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&(m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X53)))|X51!=k1_xboole_0|~r1_tarski(k2_relset_1(X51,X52,X54),X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.20/0.43  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  fof(c_0_21, negated_conjecture, (~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(m1_subset_1(esk8_0,esk4_0)&(r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))&(esk4_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)!=k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.43  fof(c_0_22, plain, ![X41, X42, X43, X44, X45, X46]:(v1_xboole_0(X43)|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X41)))|(~m1_subset_1(X46,X42)|(~r1_tarski(k2_relset_1(X42,X43,X44),k1_relset_1(X43,X41,X45))|(X42=k1_xboole_0|k1_funct_1(k8_funct_2(X42,X43,X41,X44,X45),X46)=k1_funct_1(X45,k1_funct_1(X44,X46)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.20/0.43  fof(c_0_23, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.43  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_26, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_30, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_34, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  fof(c_0_35, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|(~r2_hidden(X49,X47)|(X48=k1_xboole_0|r2_hidden(k1_funct_1(X50,X49),X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.20/0.43  cnf(c_0_36, plain, (X1=k1_xboole_0|m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k2_relset_1(X3,X1,X2))))|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(esk6_0,esk4_0,X1)|~r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.20/0.43  fof(c_0_38, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0),X3)=k1_funct_1(esk7_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk5_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (k1_relset_1(esk5_0,esk3_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.20/0.43  fof(c_0_41, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_43, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relset_1(esk4_0,esk5_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_28]), c_0_29])])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(esk6_0,esk4_0,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 0.20/0.43  cnf(c_0_46, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0),X3)=k1_funct_1(esk7_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk5_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_42, c_0_40])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),k2_relset_1(esk4_0,esk5_0,esk6_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_29])]), c_0_45])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.43  fof(c_0_54, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))|~m1_subset_1(X1,esk4_0)|~r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_28]), c_0_29]), c_0_27])]), c_0_49])).
% 0.20/0.43  fof(c_0_56, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  fof(c_0_57, plain, ![X38, X39, X40]:(~v1_relat_1(X39)|~v5_relat_1(X39,X38)|~v1_funct_1(X39)|(~r2_hidden(X40,k1_relat_1(X39))|k7_partfun1(X38,X39,X40)=k1_funct_1(X39,X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk8_0),k2_relset_1(esk4_0,esk5_0,esk6_0))|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.43  cnf(c_0_60, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.43  fof(c_0_61, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))|~m1_subset_1(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_51])])).
% 0.20/0.43  cnf(c_0_63, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.43  cnf(c_0_64, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_65, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk8_0),k1_relat_1(esk7_0))|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_60, c_0_31])).
% 0.20/0.43  cnf(c_0_68, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)!=k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_47])).
% 0.20/0.43  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.43  cnf(c_0_72, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (k7_partfun1(X1,esk7_0,k1_funct_1(esk6_0,esk8_0))=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))|k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|v1_xboole_0(esk4_0)|~v5_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_32])])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (v5_relat_1(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_31])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.43  fof(c_0_76, plain, ![X35, X36, X37]:(((v1_funct_1(X37)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(v1_xboole_0(X35)|v1_xboole_0(X36)))&(~v1_xboole_0(X37)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(v1_xboole_0(X35)|v1_xboole_0(X36))))&(v1_funct_2(X37,X35,X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(v1_xboole_0(X35)|v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.20/0.43  fof(c_0_77, plain, ![X25]:(~v1_xboole_0(X25)|v1_funct_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.20/0.43  fof(c_0_78, plain, ![X21, X22]:(~v1_xboole_0(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_xboole_0(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.43  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_80, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.43  cnf(c_0_81, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.20/0.43  fof(c_0_82, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.43  cnf(c_0_83, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.43  cnf(c_0_84, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.43  cnf(c_0_85, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.43  cnf(c_0_86, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.43  cnf(c_0_87, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_81])).
% 0.20/0.43  cnf(c_0_88, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.43  cnf(c_0_89, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.43  cnf(c_0_90, negated_conjecture, (esk5_0=k1_xboole_0|v1_xboole_0(esk6_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,k2_relset_1(esk4_0,esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_85, c_0_44])).
% 0.20/0.43  cnf(c_0_91, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_49])).
% 0.20/0.43  cnf(c_0_92, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_88])).
% 0.20/0.43  cnf(c_0_93, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_27]), c_0_28])]), c_0_33])).
% 0.20/0.43  cnf(c_0_94, negated_conjecture, (esk5_0=k1_xboole_0|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_72])])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, (esk5_0=k1_xboole_0|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.43  cnf(c_0_96, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_95])).
% 0.20/0.43  cnf(c_0_97, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_96]), c_0_49])).
% 0.20/0.43  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_97]), c_0_72])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 99
% 0.20/0.43  # Proof object clause steps            : 65
% 0.20/0.43  # Proof object formula steps           : 34
% 0.20/0.43  # Proof object conjectures             : 42
% 0.20/0.43  # Proof object clause conjectures      : 39
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 29
% 0.20/0.43  # Proof object initial formulas used   : 17
% 0.20/0.43  # Proof object generating inferences   : 28
% 0.20/0.43  # Proof object simplifying inferences  : 39
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 17
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 41
% 0.20/0.43  # Removed in clause preprocessing      : 4
% 0.20/0.43  # Initial clauses in saturation        : 37
% 0.20/0.43  # Processed clauses                    : 273
% 0.20/0.43  # ...of these trivial                  : 2
% 0.20/0.43  # ...subsumed                          : 37
% 0.20/0.43  # ...remaining for further processing  : 234
% 0.20/0.43  # Other redundant clauses eliminated   : 6
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 49
% 0.20/0.43  # Backward-rewritten                   : 86
% 0.20/0.43  # Generated clauses                    : 459
% 0.20/0.43  # ...of the previous two non-trivial   : 462
% 0.20/0.43  # Contextual simplify-reflections      : 9
% 0.20/0.43  # Paramodulations                      : 453
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 6
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 58
% 0.20/0.43  #    Positive orientable unit clauses  : 13
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 2
% 0.20/0.43  #    Non-unit-clauses                  : 43
% 0.20/0.43  # Current number of unprocessed clauses: 179
% 0.20/0.43  # ...number of literals in the above   : 673
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 170
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 4378
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 1365
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 92
% 0.20/0.43  # Unit Clause-clause subsumption calls : 43
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 10
% 0.20/0.43  # BW rewrite match successes           : 4
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 12341
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.085 s
% 0.20/0.43  # System time              : 0.007 s
% 0.20/0.43  # Total time               : 0.092 s
% 0.20/0.43  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
