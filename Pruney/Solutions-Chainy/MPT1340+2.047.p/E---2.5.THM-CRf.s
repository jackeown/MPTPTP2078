%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 (15827 expanded)
%              Number of clauses        :   99 (5644 expanded)
%              Number of leaves         :   21 (4013 expanded)
%              Depth                    :   25
%              Number of atoms          :  552 (84443 expanded)
%              Number of equality atoms :   89 (11525 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc7_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2)
        & v2_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v2_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(t48_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(t64_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X2) = k1_relat_1(X1)
              & k5_relat_1(X2,X1) = k6_relat_1(k2_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_tops_2])).

fof(c_0_22,plain,(
    ! [X30,X31] :
      ( ( ~ v1_partfun1(X31,X30)
        | k1_relat_1(X31) = X30
        | ~ v1_relat_1(X31)
        | ~ v4_relat_1(X31,X30) )
      & ( k1_relat_1(X31) != X30
        | v1_partfun1(X31,X30)
        | ~ v1_relat_1(X31)
        | ~ v4_relat_1(X31,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

fof(c_0_23,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k2_relset_1(X24,X25,X26) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_24,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_25,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_27,plain,(
    ! [X11] :
      ( ( v1_relat_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( v1_funct_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_28,plain,(
    ! [X41] :
      ( ~ l1_struct_0(X41)
      | k2_struct_0(X41) = u1_struct_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_29,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_33,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_34,plain,(
    ! [X21,X22,X23] :
      ( ( v4_relat_1(X23,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( v5_relat_1(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_35,plain,(
    ! [X39,X40] :
      ( ( v1_funct_1(X40)
        | ~ r1_tarski(k2_relat_1(X40),X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( v1_funct_2(X40,k1_relat_1(X40),X39)
        | ~ r1_tarski(k2_relat_1(X40),X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X40),X39)))
        | ~ r1_tarski(k2_relat_1(X40),X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_36,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] :
      ( ( v1_funct_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | v1_xboole_0(X28) )
      & ( v1_partfun1(X29,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | v1_xboole_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_38,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( k2_struct_0(esk2_0) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_46,plain,(
    ! [X36,X37,X38] :
      ( ( v1_funct_1(k2_funct_1(X38))
        | ~ v2_funct_1(X38)
        | k2_relset_1(X36,X37,X38) != X37
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v1_funct_2(k2_funct_1(X38),X37,X36)
        | ~ v2_funct_1(X38)
        | k2_relset_1(X36,X37,X38) != X37
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( m1_subset_1(k2_funct_1(X38),k1_zfmisc_1(k2_zfmisc_1(X37,X36)))
        | ~ v2_funct_1(X38)
        | k2_relset_1(X36,X37,X38) != X37
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_47,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X42] :
      ( v2_struct_0(X42)
      | ~ l1_struct_0(X42)
      | ~ v1_xboole_0(u1_struct_0(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_51,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_56,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_45])])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_30]),c_0_52]),c_0_53])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_64,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_53]),c_0_57])])).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_45])])).

cnf(c_0_68,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_70,plain,(
    ! [X13,X14] :
      ( ( v1_relat_1(k5_relat_1(X13,X14))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X14) )
      & ( v2_funct_1(k5_relat_1(X13,X14))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).

fof(c_0_71,plain,(
    ! [X18] :
      ( ( k5_relat_1(X18,k2_funct_1(X18)) = k6_relat_1(k1_relat_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k5_relat_1(k2_funct_1(X18),X18) = k6_relat_1(k2_relat_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_72,plain,(
    ! [X12] :
      ( ( v1_relat_1(k2_funct_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X12) )
      & ( v1_funct_1(k2_funct_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X12) )
      & ( v2_funct_1(k2_funct_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_73,negated_conjecture,
    ( v1_partfun1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_43])]),c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_30])).

cnf(c_0_75,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk2_0)
    | ~ v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_30]),c_0_31]),c_0_42]),c_0_55]),c_0_52]),c_0_56]),c_0_53])])).

cnf(c_0_78,plain,
    ( v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_39]),c_0_40]),c_0_69])).

cnf(c_0_79,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_73]),c_0_74]),c_0_57])])).

cnf(c_0_83,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | v1_xboole_0(k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_60])).

cnf(c_0_84,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk2_0)
    | ~ v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_55]),c_0_56]),c_0_53]),c_0_57])])).

fof(c_0_87,plain,(
    ! [X15,X16] :
      ( ( v2_funct_1(X16)
        | ~ v2_funct_1(k5_relat_1(X16,X15))
        | k2_relat_1(X16) != k1_relat_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v2_funct_1(X15)
        | ~ v2_funct_1(k5_relat_1(X16,X15))
        | k2_relat_1(X16) != k1_relat_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_88,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_40]),c_0_69]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk1_0)) = k5_relat_1(esk3_0,k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_82]),c_0_56]),c_0_53]),c_0_57])])).

cnf(c_0_90,plain,
    ( v1_partfun1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | v1_xboole_0(k2_relat_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_69]),c_0_40])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_30]),c_0_31]),c_0_42]),c_0_55]),c_0_52]),c_0_56]),c_0_53])])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_93,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | k2_relat_1(X2) != k1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_82]),c_0_89]),c_0_56]),c_0_53]),c_0_57])])).

cnf(c_0_95,plain,
    ( k2_relset_1(k1_relat_1(X1),X2,X1) = k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_48])).

cnf(c_0_96,negated_conjecture,
    ( v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))))
    | v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),X1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_92]),c_0_91]),c_0_77])])).

cnf(c_0_98,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_92]),c_0_55]),c_0_53]),c_0_91]),c_0_57]),c_0_77])])).

cnf(c_0_99,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),X1,k2_funct_1(esk3_0)) = k2_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_92]),c_0_91]),c_0_77])])).

cnf(c_0_100,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_101,negated_conjecture,
    ( v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))))
    | v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_77])])).

cnf(c_0_102,negated_conjecture,
    ( v1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))
    | k2_relset_1(u1_struct_0(esk2_0),X1,k2_funct_1(esk3_0)) != X1
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),X1)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_97]),c_0_98]),c_0_91])])).

cnf(c_0_103,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),k2_relat_1(k2_funct_1(esk3_0)),k2_funct_1(esk3_0)) = k2_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_60])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),k2_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_92]),c_0_91]),c_0_77])])).

cnf(c_0_105,negated_conjecture,
    ( v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),k2_relat_1(k2_funct_1(esk3_0)))
    | v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_39]),c_0_91]),c_0_77])]),c_0_98])])).

cnf(c_0_106,negated_conjecture,
    ( v1_relat_1(k2_funct_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_60]),c_0_103]),c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))) = k2_relat_1(k2_funct_1(esk3_0))
    | v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),k2_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_105]),c_0_106])])).

cnf(c_0_108,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_109,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))) = k2_relat_1(k2_funct_1(esk3_0))
    | v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_78]),c_0_98]),c_0_91]),c_0_77])])).

cnf(c_0_110,negated_conjecture,
    ( v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))
    | v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_108]),c_0_82]),c_0_56]),c_0_53]),c_0_57])])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))) = k2_relat_1(k2_funct_1(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_108]),c_0_92]),c_0_98]),c_0_91]),c_0_77])])).

cnf(c_0_112,negated_conjecture,
    ( v1_funct_1(k2_funct_1(k2_funct_1(esk3_0)))
    | k2_relset_1(u1_struct_0(esk2_0),X1,k2_funct_1(esk3_0)) != X1
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),X1)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_97]),c_0_98]),c_0_91])])).

cnf(c_0_113,negated_conjecture,
    ( v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_108]),c_0_92]),c_0_98]),c_0_91]),c_0_77])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))) = k2_relat_1(k2_funct_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_111]),c_0_43])]),c_0_63])).

cnf(c_0_115,negated_conjecture,
    ( v1_funct_1(k2_funct_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_60]),c_0_103]),c_0_104])])).

fof(c_0_116,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,X43,X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k2_relset_1(X43,X44,X45) != X44
      | ~ v2_funct_1(X45)
      | k2_tops_2(X43,X44,X45) = k2_funct_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_117,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))) = u1_struct_0(esk1_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_113]),c_0_106])])).

cnf(c_0_118,negated_conjecture,
    ( v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),k2_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_114]),c_0_115]),c_0_106])])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_120,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_121,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_122,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk1_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_117,c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_108]),c_0_82]),c_0_56]),c_0_53]),c_0_57])])).

cnf(c_0_124,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_31]),c_0_42]),c_0_55]),c_0_52]),c_0_56]),c_0_53]),c_0_30])])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_30]),c_0_31]),c_0_42]),c_0_55]),c_0_52]),c_0_56]),c_0_53])])).

fof(c_0_126,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v2_funct_1(X19)
      | k2_relat_1(X20) != k1_relat_1(X19)
      | k5_relat_1(X20,X19) != k6_relat_1(k2_relat_1(X19))
      | X20 = k2_funct_1(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_127,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk1_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])])).

cnf(c_0_128,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ v2_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_120]),c_0_125]),c_0_91])])).

cnf(c_0_129,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_127]),c_0_43])]),c_0_63])).

cnf(c_0_131,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_98])])).

cnf(c_0_132,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_108]),c_0_82]),c_0_82]),c_0_56]),c_0_53]),c_0_57])])).

cnf(c_0_133,negated_conjecture,
    ( X1 = k2_funct_1(k2_funct_1(esk3_0))
    | k5_relat_1(X1,k2_funct_1(esk3_0)) != k5_relat_1(esk3_0,k2_funct_1(esk3_0))
    | k2_relat_1(X1) != u1_struct_0(esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_89]),c_0_92]),c_0_98]),c_0_91]),c_0_77])])).

cnf(c_0_134,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132])])).

cnf(c_0_135,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_133]),c_0_55]),c_0_53]),c_0_57])])).

fof(c_0_136,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ r2_funct_2(X32,X33,X34,X35)
        | X34 = X35
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != X35
        | r2_funct_2(X32,X33,X34,X35)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_138,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_58]),c_0_31]),c_0_42]),c_0_55]),c_0_52]),c_0_56]),c_0_53]),c_0_30])])).

cnf(c_0_140,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_52]),c_0_53]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t64_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 0.20/0.39  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.39  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.39  fof(fc7_funct_1, axiom, ![X1, X2]:((((((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))&v2_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v2_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_funct_1)).
% 0.20/0.39  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.20/0.39  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.20/0.39  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 0.20/0.39  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.20/0.39  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 0.20/0.39  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.20/0.39  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3)))))), inference(assume_negation,[status(cth)],[t64_tops_2])).
% 0.20/0.39  fof(c_0_22, plain, ![X30, X31]:((~v1_partfun1(X31,X30)|k1_relat_1(X31)=X30|(~v1_relat_1(X31)|~v4_relat_1(X31,X30)))&(k1_relat_1(X31)!=X30|v1_partfun1(X31,X30)|(~v1_relat_1(X31)|~v4_relat_1(X31,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.39  fof(c_0_23, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k2_relset_1(X24,X25,X26)=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  fof(c_0_24, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)&v2_funct_1(esk3_0))&~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.20/0.39  cnf(c_0_25, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  fof(c_0_26, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_relat_1(X17)=k2_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.39  fof(c_0_27, plain, ![X11]:((v1_relat_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(v1_funct_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.39  fof(c_0_28, plain, ![X41]:(~l1_struct_0(X41)|k2_struct_0(X41)=u1_struct_0(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.39  cnf(c_0_29, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_32, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.39  fof(c_0_33, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.39  fof(c_0_34, plain, ![X21, X22, X23]:((v4_relat_1(X23,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(v5_relat_1(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  fof(c_0_35, plain, ![X39, X40]:(((v1_funct_1(X40)|~r1_tarski(k2_relat_1(X40),X39)|(~v1_relat_1(X40)|~v1_funct_1(X40)))&(v1_funct_2(X40,k1_relat_1(X40),X39)|~r1_tarski(k2_relat_1(X40),X39)|(~v1_relat_1(X40)|~v1_funct_1(X40))))&(m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X40),X39)))|~r1_tarski(k2_relat_1(X40),X39)|(~v1_relat_1(X40)|~v1_funct_1(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.39  fof(c_0_36, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  fof(c_0_37, plain, ![X27, X28, X29]:((v1_funct_1(X29)|(~v1_funct_1(X29)|~v1_funct_2(X29,X27,X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_xboole_0(X28))&(v1_partfun1(X29,X27)|(~v1_funct_1(X29)|~v1_funct_2(X29,X27,X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_xboole_0(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.39  cnf(c_0_38, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_39, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_40, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_41, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (k2_struct_0(esk2_0)=k2_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_44, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_45, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  fof(c_0_46, plain, ![X36, X37, X38]:(((v1_funct_1(k2_funct_1(X38))|(~v2_funct_1(X38)|k2_relset_1(X36,X37,X38)!=X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(v1_funct_2(k2_funct_1(X38),X37,X36)|(~v2_funct_1(X38)|k2_relset_1(X36,X37,X38)!=X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&(m1_subset_1(k2_funct_1(X38),k1_zfmisc_1(k2_zfmisc_1(X37,X36)))|(~v2_funct_1(X38)|k2_relset_1(X36,X37,X38)!=X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.39  cnf(c_0_47, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  fof(c_0_50, plain, ![X42]:(v2_struct_0(X42)|~l1_struct_0(X42)|~v1_xboole_0(u1_struct_0(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.39  cnf(c_0_51, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_54, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (k2_relat_1(esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_45])])).
% 0.20/0.39  cnf(c_0_58, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_59, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_61, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v1_partfun1(esk3_0,u1_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_30]), c_0_52]), c_0_53])])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_64, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_65, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (v1_partfun1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))|~v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  cnf(c_0_67, plain, (v1_relat_1(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_58]), c_0_45])])).
% 0.20/0.39  cnf(c_0_68, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.39  cnf(c_0_69, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_70, plain, ![X13, X14]:((v1_relat_1(k5_relat_1(X13,X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)|~v2_funct_1(X13)|~v1_relat_1(X14)|~v1_funct_1(X14)|~v2_funct_1(X14)))&(v2_funct_1(k5_relat_1(X13,X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)|~v2_funct_1(X13)|~v1_relat_1(X14)|~v1_funct_1(X14)|~v2_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).
% 0.20/0.39  fof(c_0_71, plain, ![X18]:((k5_relat_1(X18,k2_funct_1(X18))=k6_relat_1(k1_relat_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k5_relat_1(k2_funct_1(X18),X18)=k6_relat_1(k2_relat_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.20/0.39  fof(c_0_72, plain, ![X12]:(((v1_relat_1(k2_funct_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12)|~v2_funct_1(X12)))&(v1_funct_1(k2_funct_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12)|~v2_funct_1(X12))))&(v2_funct_1(k2_funct_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12)|~v2_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (v1_partfun1(esk3_0,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_43])]), c_0_63])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_47, c_0_30])).
% 0.20/0.39  cnf(c_0_75, plain, (v1_partfun1(X1,k1_relat_1(X1))|v1_xboole_0(X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_64])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk2_0)|~v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_30]), c_0_31]), c_0_42]), c_0_55]), c_0_52]), c_0_56]), c_0_53])])).
% 0.20/0.39  cnf(c_0_78, plain, (v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_39]), c_0_40]), c_0_69])).
% 0.20/0.39  cnf(c_0_79, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.39  cnf(c_0_80, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.39  cnf(c_0_81, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_73]), c_0_74]), c_0_57])])).
% 0.20/0.39  cnf(c_0_83, plain, (v1_partfun1(X1,k1_relat_1(X1))|v1_xboole_0(k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_60])).
% 0.20/0.39  cnf(c_0_84, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk2_0)|~v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_55]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  fof(c_0_87, plain, ![X15, X16]:((v2_funct_1(X16)|(~v2_funct_1(k5_relat_1(X16,X15))|k2_relat_1(X16)!=k1_relat_1(X15))|(~v1_relat_1(X16)|~v1_funct_1(X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v2_funct_1(X15)|(~v2_funct_1(k5_relat_1(X16,X15))|k2_relat_1(X16)!=k1_relat_1(X15))|(~v1_relat_1(X16)|~v1_funct_1(X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 0.20/0.39  cnf(c_0_88, plain, (v2_funct_1(k6_relat_1(k1_relat_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_40]), c_0_69]), c_0_81])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (k6_relat_1(u1_struct_0(esk1_0))=k5_relat_1(esk3_0,k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_82]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  cnf(c_0_90, plain, (v1_partfun1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|v1_xboole_0(k2_relat_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_69]), c_0_40])).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_30]), c_0_31]), c_0_42]), c_0_55]), c_0_52]), c_0_56]), c_0_53])])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.20/0.39  cnf(c_0_93, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X2,X1))|k2_relat_1(X2)!=k1_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_82]), c_0_89]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  cnf(c_0_95, plain, (k2_relset_1(k1_relat_1(X1),X2,X1)=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_29, c_0_48])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))))|v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),X1)))|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_92]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, (v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_92]), c_0_55]), c_0_53]), c_0_91]), c_0_57]), c_0_77])])).
% 0.20/0.39  cnf(c_0_99, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),X1,k2_funct_1(esk3_0))=k2_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_92]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_100, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_60])).
% 0.20/0.39  cnf(c_0_101, negated_conjecture, (v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),k1_relat_1(k2_funct_1(k2_funct_1(esk3_0))))|v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_77])])).
% 0.20/0.39  cnf(c_0_102, negated_conjecture, (v1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))|k2_relset_1(u1_struct_0(esk2_0),X1,k2_funct_1(esk3_0))!=X1|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),X1)|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_97]), c_0_98]), c_0_91])])).
% 0.20/0.39  cnf(c_0_103, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),k2_relat_1(k2_funct_1(esk3_0)),k2_funct_1(esk3_0))=k2_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_99, c_0_60])).
% 0.20/0.39  cnf(c_0_104, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),k2_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_92]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_105, negated_conjecture, (v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),k2_relat_1(k2_funct_1(esk3_0)))|v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_39]), c_0_91]), c_0_77])]), c_0_98])])).
% 0.20/0.39  cnf(c_0_106, negated_conjecture, (v1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_60]), c_0_103]), c_0_104])])).
% 0.20/0.39  cnf(c_0_107, negated_conjecture, (k1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))=k2_relat_1(k2_funct_1(esk3_0))|v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))|~v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),k2_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_105]), c_0_106])])).
% 0.20/0.39  cnf(c_0_108, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_109, negated_conjecture, (k1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))=k2_relat_1(k2_funct_1(esk3_0))|v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_78]), c_0_98]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_110, negated_conjecture, (v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))|v1_xboole_0(k2_relat_1(k2_funct_1(k2_funct_1(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_108]), c_0_82]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  cnf(c_0_111, negated_conjecture, (k1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))=k2_relat_1(k2_funct_1(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_108]), c_0_92]), c_0_98]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_112, negated_conjecture, (v1_funct_1(k2_funct_1(k2_funct_1(esk3_0)))|k2_relset_1(u1_struct_0(esk2_0),X1,k2_funct_1(esk3_0))!=X1|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),X1)|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_97]), c_0_98]), c_0_91])])).
% 0.20/0.39  cnf(c_0_113, negated_conjecture, (v1_partfun1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_108]), c_0_92]), c_0_98]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_114, negated_conjecture, (k1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))=k2_relat_1(k2_funct_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_111]), c_0_43])]), c_0_63])).
% 0.20/0.39  cnf(c_0_115, negated_conjecture, (v1_funct_1(k2_funct_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_60]), c_0_103]), c_0_104])])).
% 0.20/0.39  fof(c_0_116, plain, ![X43, X44, X45]:(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|(k2_relset_1(X43,X44,X45)!=X44|~v2_funct_1(X45)|k2_tops_2(X43,X44,X45)=k2_funct_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.20/0.39  cnf(c_0_117, negated_conjecture, (k1_relat_1(k2_funct_1(k2_funct_1(esk3_0)))=u1_struct_0(esk1_0)|v1_xboole_0(u1_struct_0(esk2_0))|~v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_113]), c_0_106])])).
% 0.20/0.39  cnf(c_0_118, negated_conjecture, (v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),k2_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_114]), c_0_115]), c_0_106])])).
% 0.20/0.39  cnf(c_0_119, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_120, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.20/0.39  cnf(c_0_121, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_122, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk1_0)|v1_xboole_0(u1_struct_0(esk2_0))|~v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_117, c_0_114])).
% 0.20/0.39  cnf(c_0_123, negated_conjecture, (v4_relat_1(k2_funct_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_108]), c_0_82]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  cnf(c_0_124, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_31]), c_0_42]), c_0_55]), c_0_52]), c_0_56]), c_0_53]), c_0_30])])).
% 0.20/0.39  cnf(c_0_125, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_30]), c_0_31]), c_0_42]), c_0_55]), c_0_52]), c_0_56]), c_0_53])])).
% 0.20/0.39  fof(c_0_126, plain, ![X19, X20]:(~v1_relat_1(X19)|~v1_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v2_funct_1(X19)|k2_relat_1(X20)!=k1_relat_1(X19)|k5_relat_1(X20,X19)!=k6_relat_1(k2_relat_1(X19))|X20=k2_funct_1(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.20/0.39  cnf(c_0_127, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk1_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123])])).
% 0.20/0.39  cnf(c_0_128, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~v2_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_120]), c_0_125]), c_0_91])])).
% 0.20/0.39  cnf(c_0_129, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_126])).
% 0.20/0.39  cnf(c_0_130, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_127]), c_0_43])]), c_0_63])).
% 0.20/0.39  cnf(c_0_131, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_98])])).
% 0.20/0.39  cnf(c_0_132, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_108]), c_0_82]), c_0_82]), c_0_56]), c_0_53]), c_0_57])])).
% 0.20/0.39  cnf(c_0_133, negated_conjecture, (X1=k2_funct_1(k2_funct_1(esk3_0))|k5_relat_1(X1,k2_funct_1(esk3_0))!=k5_relat_1(esk3_0,k2_funct_1(esk3_0))|k2_relat_1(X1)!=u1_struct_0(esk2_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_89]), c_0_92]), c_0_98]), c_0_91]), c_0_77])])).
% 0.20/0.39  cnf(c_0_134, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132])])).
% 0.20/0.39  cnf(c_0_135, negated_conjecture, (k2_funct_1(k2_funct_1(esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_133]), c_0_55]), c_0_53]), c_0_57])])).
% 0.20/0.39  fof(c_0_136, plain, ![X32, X33, X34, X35]:((~r2_funct_2(X32,X33,X34,X35)|X34=X35|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(X34!=X35|r2_funct_2(X32,X33,X34,X35)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.20/0.39  cnf(c_0_137, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_134, c_0_135])).
% 0.20/0.39  cnf(c_0_138, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_136])).
% 0.20/0.39  cnf(c_0_139, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_58]), c_0_31]), c_0_42]), c_0_55]), c_0_52]), c_0_56]), c_0_53]), c_0_30])])).
% 0.20/0.39  cnf(c_0_140, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_138])).
% 0.20/0.39  cnf(c_0_141, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_52]), c_0_53]), c_0_30])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 142
% 0.20/0.39  # Proof object clause steps            : 99
% 0.20/0.39  # Proof object formula steps           : 43
% 0.20/0.39  # Proof object conjectures             : 62
% 0.20/0.39  # Proof object clause conjectures      : 59
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 34
% 0.20/0.39  # Proof object initial formulas used   : 21
% 0.20/0.39  # Proof object generating inferences   : 54
% 0.20/0.39  # Proof object simplifying inferences  : 188
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 21
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 46
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 44
% 0.20/0.39  # Processed clauses                    : 223
% 0.20/0.39  # ...of these trivial                  : 5
% 0.20/0.39  # ...subsumed                          : 21
% 0.20/0.39  # ...remaining for further processing  : 197
% 0.20/0.39  # Other redundant clauses eliminated   : 4
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 7
% 0.20/0.39  # Backward-rewritten                   : 51
% 0.20/0.39  # Generated clauses                    : 237
% 0.20/0.39  # ...of the previous two non-trivial   : 193
% 0.20/0.39  # Contextual simplify-reflections      : 17
% 0.20/0.39  # Paramodulations                      : 231
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 6
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 94
% 0.20/0.39  #    Positive orientable unit clauses  : 31
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 59
% 0.20/0.39  # Current number of unprocessed clauses: 53
% 0.20/0.39  # ...number of literals in the above   : 287
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 99
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1713
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 247
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 43
% 0.20/0.39  # Unit Clause-clause subsumption calls : 72
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 19
% 0.20/0.39  # BW rewrite match successes           : 16
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9637
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.045 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.049 s
% 0.20/0.39  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
