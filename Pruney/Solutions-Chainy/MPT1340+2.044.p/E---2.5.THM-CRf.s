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
% DateTime   : Thu Dec  3 11:13:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  175 (2550 expanded)
%              Number of clauses        :  115 ( 919 expanded)
%              Number of leaves         :   30 ( 651 expanded)
%              Depth                    :   23
%              Number of atoms          :  627 (12922 expanded)
%              Number of equality atoms :  160 (1769 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t177_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v2_funct_1(X1)
            & r1_tarski(X2,k1_relat_1(X1)) )
         => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(reflexivity_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_funct_2(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(c_0_30,negated_conjecture,(
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

fof(c_0_31,plain,(
    ! [X34,X35,X36] :
      ( ( v1_funct_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | v1_xboole_0(X35) )
      & ( v1_partfun1(X36,X34)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_32,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

fof(c_0_33,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_34,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_35,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_36,plain,(
    ! [X37,X38] :
      ( ( ~ v1_partfun1(X38,X37)
        | k1_relat_1(X38) = X37
        | ~ v1_relat_1(X38)
        | ~ v4_relat_1(X38,X37) )
      & ( k1_relat_1(X38) != X37
        | v1_partfun1(X38,X37)
        | ~ v1_relat_1(X38)
        | ~ v4_relat_1(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_37,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X53] :
      ( v2_struct_0(X53)
      | ~ l1_struct_0(X53)
      | ~ v1_xboole_0(u1_struct_0(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_45,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_43])])).

fof(c_0_49,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_50,plain,(
    ! [X12,X13] :
      ( ( ~ v4_relat_1(X13,X12)
        | r1_tarski(k1_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_relat_1(X13),X12)
        | v4_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_55,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),c_0_54])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_61,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1_0),X1)
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_48])])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_59])).

fof(c_0_64,plain,(
    ! [X51] :
      ( ~ l1_struct_0(X51)
      | k2_struct_0(X51) = u1_struct_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_65,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(X1) = u1_struct_0(esk1_0)
    | ~ v4_relat_1(X1,u1_struct_0(esk1_0))
    | ~ v4_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_63])).

fof(c_0_69,plain,(
    ! [X25] :
      ( ( k2_relat_1(X25) = k1_relat_1(k2_funct_1(X25))
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_relat_1(X25) = k2_relat_1(k2_funct_1(X25))
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_70,plain,(
    ! [X18] :
      ( ( v1_relat_1(k2_funct_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(k2_funct_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_71,plain,(
    ! [X17] :
      ( ( k1_relat_1(X17) != k1_xboole_0
        | k2_relat_1(X17) = k1_xboole_0
        | ~ v1_relat_1(X17) )
      & ( k2_relat_1(X17) != k1_xboole_0
        | k1_relat_1(X17) = k1_xboole_0
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_72,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( k2_struct_0(esk2_0) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_38]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(X1) = u1_struct_0(esk1_0)
    | ~ v4_relat_1(esk3_0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_53])])).

fof(c_0_79,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_80,plain,(
    ! [X47,X48,X49] :
      ( ( k5_relat_1(X49,k2_funct_1(X49)) = k6_partfun1(X47)
        | X48 = k1_xboole_0
        | k2_relset_1(X47,X48,X49) != X48
        | ~ v2_funct_1(X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( k5_relat_1(k2_funct_1(X49),X49) = k6_partfun1(X48)
        | X48 = k1_xboole_0
        | k2_relset_1(X47,X48,X49) != X48
        | ~ v2_funct_1(X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_81,plain,(
    ! [X39] : k6_partfun1(X39) = k6_relat_1(X39) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(X1) = u1_struct_0(esk1_0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(esk3_0,k2_relat_1(X1))
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_84,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_48])])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_87,plain,(
    ! [X50] :
      ( ( v1_funct_1(X50)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( v1_funct_2(X50,k1_relat_1(X50),k2_relat_1(X50))
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X50),k2_relat_1(X50))))
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_88,plain,(
    ! [X44,X45,X46] :
      ( ( v1_funct_1(k2_funct_1(X46))
        | ~ v2_funct_1(X46)
        | k2_relset_1(X44,X45,X46) != X45
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(k2_funct_1(X46),X45,X44)
        | ~ v2_funct_1(X46)
        | k2_relset_1(X44,X45,X46) != X45
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(k2_funct_1(X46),k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | ~ v2_funct_1(X46)
        | k2_relset_1(X44,X45,X46) != X45
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_89,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k9_relat_1(X16,k1_relat_1(X16)) = k2_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_90,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | ~ v4_relat_1(esk3_0,u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_78]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_93,negated_conjecture,
    ( v4_relat_1(esk3_0,X1)
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_48]),c_0_86])])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_96,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_97,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v2_funct_1(X21)
      | ~ r1_tarski(X22,k1_relat_1(X21))
      | k9_relat_1(k2_funct_1(X21),k9_relat_1(X21,X22)) = X22 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).

cnf(c_0_98,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_100,plain,(
    ! [X19] :
      ( v1_relat_1(k6_relat_1(X19))
      & v2_funct_1(k6_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_101,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_63])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_38]),c_0_66]),c_0_73]),c_0_78]),c_0_39]),c_0_83]),c_0_40])])).

cnf(c_0_105,plain,
    ( k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( k9_relat_1(esk3_0,u1_struct_0(esk1_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_58]),c_0_78]),c_0_48])])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_99])).

fof(c_0_108,plain,(
    ! [X23,X24] :
      ( ( v2_funct_1(X24)
        | ~ v2_funct_1(k5_relat_1(X24,X23))
        | k2_relat_1(X24) != k1_relat_1(X23)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( v2_funct_1(X23)
        | ~ v2_funct_1(k5_relat_1(X24,X23))
        | k2_relat_1(X24) != k1_relat_1(X23)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_109,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk2_0)) = k5_relat_1(k2_funct_1(esk3_0),esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_38]),c_0_66]),c_0_73]),c_0_78]),c_0_39]),c_0_83]),c_0_40])])).

cnf(c_0_111,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | k1_relat_1(k2_funct_1(esk3_0)) != k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_112,plain,
    ( k9_relat_1(k2_funct_1(X1),k2_relat_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_75]),c_0_76])).

cnf(c_0_113,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_83]),c_0_40]),c_0_48]),c_0_58]),c_0_107])])).

cnf(c_0_114,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_funct_1(k5_relat_1(k2_funct_1(esk3_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

fof(c_0_116,plain,(
    ! [X52] :
      ( ~ v2_struct_0(X52)
      | ~ l1_struct_0(X52)
      | v1_xboole_0(u1_struct_0(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

cnf(c_0_117,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_75]),c_0_78]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_118,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_58])).

cnf(c_0_119,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_120,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_121,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_122,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_78]),c_0_113]),c_0_83]),c_0_40]),c_0_48])])).

fof(c_0_123,plain,(
    ! [X54,X55,X56] :
      ( ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X54,X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k2_relset_1(X54,X55,X56) != X55
      | ~ v2_funct_1(X56)
      | k2_tops_2(X54,X55,X56) = k2_funct_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_124,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk3_0))
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_58]),c_0_40]),c_0_104]),c_0_48])])).

cnf(c_0_125,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_126,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_76]),c_0_40]),c_0_48])])).

cnf(c_0_127,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_118]),c_0_119]),c_0_120])])).

cnf(c_0_128,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_121])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_122]),c_0_104])])).

cnf(c_0_130,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_131,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_132,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_133,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_134,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk3_0))
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_76]),c_0_40]),c_0_48])])).

cnf(c_0_135,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_119])]),c_0_127])).

cnf(c_0_136,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_137,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_138,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_75]),c_0_76])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_75]),c_0_78]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_140,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_130]),c_0_76]),c_0_131])).

cnf(c_0_141,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_66]),c_0_73]),c_0_78]),c_0_39]),c_0_83]),c_0_40]),c_0_38])])).

cnf(c_0_142,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_130]),c_0_58]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_143,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_135]),c_0_53])]),c_0_54])).

cnf(c_0_144,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_130]),c_0_76]),c_0_131])).

fof(c_0_145,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | ~ v2_funct_1(X26)
      | k2_relat_1(X27) != k1_relat_1(X26)
      | k5_relat_1(X27,X26) != k6_relat_1(k2_relat_1(X26))
      | X27 = k2_funct_1(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

fof(c_0_146,plain,(
    ! [X20] :
      ( ( v1_relat_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X20) )
      & ( v1_funct_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X20) )
      & ( v2_funct_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_147,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_137,c_0_91])).

cnf(c_0_148,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_78]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_149,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_139])).

cnf(c_0_150,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_58]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_151,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ v2_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_133]),c_0_104])])).

cnf(c_0_152,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_153,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_58]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_154,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_145])).

cnf(c_0_155,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_146])).

cnf(c_0_156,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk1_0)) = k5_relat_1(esk3_0,k2_funct_1(esk3_0))
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_38]),c_0_66]),c_0_73]),c_0_78]),c_0_39]),c_0_83]),c_0_40])])).

cnf(c_0_157,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk2_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_148]),c_0_149])).

cnf(c_0_158,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_150]),c_0_43])])).

cnf(c_0_159,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_152])])).

cnf(c_0_160,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_75]),c_0_78]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_75]),c_0_78]),c_0_83]),c_0_40]),c_0_48])])).

cnf(c_0_162,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(X1,k2_funct_1(X2)) != k6_relat_1(k1_relat_1(X2))
    | k2_relat_1(X1) != k1_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_130]),c_0_76]),c_0_131]),c_0_155])).

cnf(c_0_163,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk1_0)) = k5_relat_1(esk3_0,k2_funct_1(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_156,c_0_143])).

cnf(c_0_164,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_158])])).

cnf(c_0_165,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160])])).

cnf(c_0_166,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_161]),c_0_122])).

cnf(c_0_167,negated_conjecture,
    ( X1 = k2_funct_1(k2_funct_1(esk3_0))
    | k5_relat_1(X1,k2_funct_1(esk3_0)) != k5_relat_1(esk3_0,k2_funct_1(esk3_0))
    | k2_relat_1(X1) != u1_struct_0(esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_58]),c_0_163]),c_0_164]),c_0_83]),c_0_40]),c_0_48])])).

fof(c_0_168,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X40,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,X40,X41)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | r2_funct_2(X40,X41,X42,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).

cnf(c_0_169,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165,c_0_161])]),c_0_166])])).

cnf(c_0_170,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_167]),c_0_78]),c_0_40]),c_0_48])])).

cnf(c_0_171,plain,
    ( r2_funct_2(X2,X3,X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_168])).

cnf(c_0_172,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_173,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,X1)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_174,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_173]),c_0_39]),c_0_40]),c_0_38])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.030 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t64_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 0.20/0.42  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.42  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.42  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.42  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.20/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.42  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.42  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.20/0.42  fof(t177_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 0.20/0.42  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.42  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 0.20/0.42  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.20/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.42  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 0.20/0.42  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 0.20/0.42  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.20/0.42  fof(reflexivity_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_funct_2(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 0.20/0.42  fof(c_0_30, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3)))))), inference(assume_negation,[status(cth)],[t64_tops_2])).
% 0.20/0.42  fof(c_0_31, plain, ![X34, X35, X36]:((v1_funct_1(X36)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_xboole_0(X35))&(v1_partfun1(X36,X34)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_xboole_0(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.42  fof(c_0_32, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)&v2_funct_1(esk3_0))&~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.20/0.42  fof(c_0_33, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.42  fof(c_0_34, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.42  fof(c_0_35, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.42  fof(c_0_36, plain, ![X37, X38]:((~v1_partfun1(X38,X37)|k1_relat_1(X38)=X37|(~v1_relat_1(X38)|~v4_relat_1(X38,X37)))&(k1_relat_1(X38)!=X37|v1_partfun1(X38,X37)|(~v1_relat_1(X38)|~v4_relat_1(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.42  cnf(c_0_37, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_41, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_42, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_43, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.42  fof(c_0_44, plain, ![X53]:(v2_struct_0(X53)|~l1_struct_0(X53)|~v1_xboole_0(u1_struct_0(X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.42  cnf(c_0_45, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (v1_partfun1(esk3_0,u1_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_38]), c_0_43])])).
% 0.20/0.42  fof(c_0_49, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.42  fof(c_0_50, plain, ![X12, X13]:((~v4_relat_1(X13,X12)|r1_tarski(k1_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k1_relat_1(X13),X12)|v4_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.42  cnf(c_0_51, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  fof(c_0_55, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.42  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), c_0_54])).
% 0.20/0.42  cnf(c_0_59, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.42  fof(c_0_60, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_relset_1(X31,X32,X33)=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.42  cnf(c_0_61, plain, (X1=k1_relat_1(X2)|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(u1_struct_0(esk1_0),X1)|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_48])])).
% 0.20/0.42  cnf(c_0_63, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_59])).
% 0.20/0.42  fof(c_0_64, plain, ![X51]:(~l1_struct_0(X51)|k2_struct_0(X51)=u1_struct_0(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.42  cnf(c_0_65, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, (k1_relat_1(X1)=u1_struct_0(esk1_0)|~v4_relat_1(X1,u1_struct_0(esk1_0))|~v4_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.42  cnf(c_0_68, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_41, c_0_63])).
% 0.20/0.42  fof(c_0_69, plain, ![X25]:((k2_relat_1(X25)=k1_relat_1(k2_funct_1(X25))|~v2_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_relat_1(X25)=k2_relat_1(k2_funct_1(X25))|~v2_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.42  fof(c_0_70, plain, ![X18]:((v1_relat_1(k2_funct_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(k2_funct_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.42  fof(c_0_71, plain, ![X17]:((k1_relat_1(X17)!=k1_xboole_0|k2_relat_1(X17)=k1_xboole_0|~v1_relat_1(X17))&(k2_relat_1(X17)!=k1_xboole_0|k1_relat_1(X17)=k1_xboole_0|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.20/0.42  cnf(c_0_72, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.42  cnf(c_0_73, negated_conjecture, (k2_struct_0(esk2_0)=k2_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_38]), c_0_66])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (k1_relat_1(X1)=u1_struct_0(esk1_0)|~v4_relat_1(esk3_0,k1_relat_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.42  cnf(c_0_75, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.42  cnf(c_0_76, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.42  cnf(c_0_77, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (k2_relat_1(esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_53])])).
% 0.20/0.42  fof(c_0_79, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  fof(c_0_80, plain, ![X47, X48, X49]:((k5_relat_1(X49,k2_funct_1(X49))=k6_partfun1(X47)|X48=k1_xboole_0|(k2_relset_1(X47,X48,X49)!=X48|~v2_funct_1(X49))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(k5_relat_1(k2_funct_1(X49),X49)=k6_partfun1(X48)|X48=k1_xboole_0|(k2_relset_1(X47,X48,X49)!=X48|~v2_funct_1(X49))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.20/0.42  fof(c_0_81, plain, ![X39]:k6_partfun1(X39)=k6_relat_1(X39), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (k2_relat_1(X1)=u1_struct_0(esk1_0)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v4_relat_1(esk3_0,k2_relat_1(X1))|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_84, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_48])])).
% 0.20/0.42  cnf(c_0_86, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.42  fof(c_0_87, plain, ![X50]:(((v1_funct_1(X50)|(~v1_relat_1(X50)|~v1_funct_1(X50)))&(v1_funct_2(X50,k1_relat_1(X50),k2_relat_1(X50))|(~v1_relat_1(X50)|~v1_funct_1(X50))))&(m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X50),k2_relat_1(X50))))|(~v1_relat_1(X50)|~v1_funct_1(X50)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.42  fof(c_0_88, plain, ![X44, X45, X46]:(((v1_funct_1(k2_funct_1(X46))|(~v2_funct_1(X46)|k2_relset_1(X44,X45,X46)!=X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(v1_funct_2(k2_funct_1(X46),X45,X44)|(~v2_funct_1(X46)|k2_relset_1(X44,X45,X46)!=X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&(m1_subset_1(k2_funct_1(X46),k1_zfmisc_1(k2_zfmisc_1(X45,X44)))|(~v2_funct_1(X46)|k2_relset_1(X44,X45,X46)!=X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.42  fof(c_0_89, plain, ![X16]:(~v1_relat_1(X16)|k9_relat_1(X16,k1_relat_1(X16))=k2_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.20/0.42  cnf(c_0_90, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.42  cnf(c_0_91, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|~v4_relat_1(esk3_0,u1_struct_0(esk2_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_78]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (v4_relat_1(esk3_0,X1)|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_48]), c_0_86])])).
% 0.20/0.42  cnf(c_0_94, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.42  cnf(c_0_95, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.42  cnf(c_0_96, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.42  fof(c_0_97, plain, ![X21, X22]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~v2_funct_1(X21)|~r1_tarski(X22,k1_relat_1(X21))|k9_relat_1(k2_funct_1(X21),k9_relat_1(X21,X22))=X22)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).
% 0.20/0.42  cnf(c_0_98, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.42  cnf(c_0_99, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  fof(c_0_100, plain, ![X19]:(v1_relat_1(k6_relat_1(X19))&v2_funct_1(k6_relat_1(X19))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.42  cnf(c_0_101, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.42  cnf(c_0_103, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_63])).
% 0.20/0.42  cnf(c_0_104, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_38]), c_0_66]), c_0_73]), c_0_78]), c_0_39]), c_0_83]), c_0_40])])).
% 0.20/0.42  cnf(c_0_105, plain, (k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (k9_relat_1(esk3_0,u1_struct_0(esk1_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_58]), c_0_78]), c_0_48])])).
% 0.20/0.42  cnf(c_0_107, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_99])).
% 0.20/0.42  fof(c_0_108, plain, ![X23, X24]:((v2_funct_1(X24)|(~v2_funct_1(k5_relat_1(X24,X23))|k2_relat_1(X24)!=k1_relat_1(X23))|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(v2_funct_1(X23)|(~v2_funct_1(k5_relat_1(X24,X23))|k2_relat_1(X24)!=k1_relat_1(X23))|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 0.20/0.42  cnf(c_0_109, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.42  cnf(c_0_110, negated_conjecture, (k6_relat_1(u1_struct_0(esk2_0))=k5_relat_1(k2_funct_1(esk3_0),esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_38]), c_0_66]), c_0_73]), c_0_78]), c_0_39]), c_0_83]), c_0_40])])).
% 0.20/0.42  cnf(c_0_111, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|k1_relat_1(k2_funct_1(esk3_0))!=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 0.20/0.42  cnf(c_0_112, plain, (k9_relat_1(k2_funct_1(X1),k2_relat_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_75]), c_0_76])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (k9_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_83]), c_0_40]), c_0_48]), c_0_58]), c_0_107])])).
% 0.20/0.42  cnf(c_0_114, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,X2))|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_funct_1(k5_relat_1(k2_funct_1(esk3_0),esk3_0))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.20/0.42  fof(c_0_116, plain, ![X52]:(~v2_struct_0(X52)|~l1_struct_0(X52)|v1_xboole_0(u1_struct_0(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_75]), c_0_78]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_58])).
% 0.20/0.42  cnf(c_0_119, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_120, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.42  cnf(c_0_121, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_122, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_78]), c_0_113]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  fof(c_0_123, plain, ![X54, X55, X56]:(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|(k2_relset_1(X54,X55,X56)!=X55|~v2_funct_1(X56)|k2_tops_2(X54,X55,X56)=k2_funct_1(X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.20/0.42  cnf(c_0_124, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk3_0))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_58]), c_0_40]), c_0_104]), c_0_48])])).
% 0.20/0.42  cnf(c_0_125, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.20/0.42  cnf(c_0_126, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_76]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_127, negated_conjecture, (v2_struct_0(esk1_0)|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_118]), c_0_119]), c_0_120])])).
% 0.20/0.42  cnf(c_0_128, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_121])).
% 0.20/0.42  cnf(c_0_129, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_122]), c_0_104])])).
% 0.20/0.42  cnf(c_0_130, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.42  cnf(c_0_131, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.42  cnf(c_0_132, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_133, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.20/0.42  cnf(c_0_134, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk3_0))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_76]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_135, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|u1_struct_0(esk2_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_119])]), c_0_127])).
% 0.20/0.42  cnf(c_0_136, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.42  cnf(c_0_137, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.42  cnf(c_0_138, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_75]), c_0_76])).
% 0.20/0.42  cnf(c_0_139, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_75]), c_0_78]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_140, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_130]), c_0_76]), c_0_131])).
% 0.20/0.42  cnf(c_0_141, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_66]), c_0_73]), c_0_78]), c_0_39]), c_0_83]), c_0_40]), c_0_38])])).
% 0.20/0.42  cnf(c_0_142, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_130]), c_0_58]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_143, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_135]), c_0_53])]), c_0_54])).
% 0.20/0.42  cnf(c_0_144, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_130]), c_0_76]), c_0_131])).
% 0.20/0.42  fof(c_0_145, plain, ![X26, X27]:(~v1_relat_1(X26)|~v1_funct_1(X26)|(~v1_relat_1(X27)|~v1_funct_1(X27)|(~v2_funct_1(X26)|k2_relat_1(X27)!=k1_relat_1(X26)|k5_relat_1(X27,X26)!=k6_relat_1(k2_relat_1(X26))|X27=k2_funct_1(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.20/0.42  fof(c_0_146, plain, ![X20]:(((v1_relat_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)|~v2_funct_1(X20)))&(v1_funct_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)|~v2_funct_1(X20))))&(v2_funct_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)|~v2_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.20/0.42  cnf(c_0_147, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_137, c_0_91])).
% 0.20/0.42  cnf(c_0_148, negated_conjecture, (v1_partfun1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))|~v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_78]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_149, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),u1_struct_0(esk2_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_139])).
% 0.20/0.42  cnf(c_0_150, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_58]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_151, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~v2_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_133]), c_0_104])])).
% 0.20/0.42  cnf(c_0_152, negated_conjecture, (v2_funct_1(k2_funct_1(esk3_0))), inference(sr,[status(thm)],[c_0_142, c_0_143])).
% 0.20/0.42  cnf(c_0_153, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_58]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_154, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_145])).
% 0.20/0.42  cnf(c_0_155, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_146])).
% 0.20/0.42  cnf(c_0_156, negated_conjecture, (k6_relat_1(u1_struct_0(esk1_0))=k5_relat_1(esk3_0,k2_funct_1(esk3_0))|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_38]), c_0_66]), c_0_73]), c_0_78]), c_0_39]), c_0_83]), c_0_40])])).
% 0.20/0.42  cnf(c_0_157, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk2_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_148]), c_0_149])).
% 0.20/0.42  cnf(c_0_158, negated_conjecture, (v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_150]), c_0_43])])).
% 0.20/0.42  cnf(c_0_159, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_152])])).
% 0.20/0.42  cnf(c_0_160, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_75]), c_0_78]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_161, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_75]), c_0_78]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_162, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(X1,k2_funct_1(X2))!=k6_relat_1(k1_relat_1(X2))|k2_relat_1(X1)!=k1_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_130]), c_0_76]), c_0_131]), c_0_155])).
% 0.20/0.42  cnf(c_0_163, negated_conjecture, (k6_relat_1(u1_struct_0(esk1_0))=k5_relat_1(esk3_0,k2_funct_1(esk3_0))), inference(sr,[status(thm)],[c_0_156, c_0_143])).
% 0.20/0.42  cnf(c_0_164, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157, c_0_158])])).
% 0.20/0.42  cnf(c_0_165, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_160])])).
% 0.20/0.42  cnf(c_0_166, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_161]), c_0_122])).
% 0.20/0.42  cnf(c_0_167, negated_conjecture, (X1=k2_funct_1(k2_funct_1(esk3_0))|k5_relat_1(X1,k2_funct_1(esk3_0))!=k5_relat_1(esk3_0,k2_funct_1(esk3_0))|k2_relat_1(X1)!=u1_struct_0(esk2_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_58]), c_0_163]), c_0_164]), c_0_83]), c_0_40]), c_0_48])])).
% 0.20/0.42  fof(c_0_168, plain, ![X40, X41, X42, X43]:(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X43)|~v1_funct_2(X43,X40,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|r2_funct_2(X40,X41,X42,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).
% 0.20/0.42  cnf(c_0_169, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165, c_0_161])]), c_0_166])])).
% 0.20/0.42  cnf(c_0_170, negated_conjecture, (k2_funct_1(k2_funct_1(esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_167]), c_0_78]), c_0_40]), c_0_48])])).
% 0.20/0.42  cnf(c_0_171, plain, (r2_funct_2(X2,X3,X1,X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_168])).
% 0.20/0.42  cnf(c_0_172, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_169, c_0_170])).
% 0.20/0.42  cnf(c_0_173, negated_conjecture, (r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,X1)|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.42  cnf(c_0_174, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_173]), c_0_39]), c_0_40]), c_0_38])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 175
% 0.20/0.42  # Proof object clause steps            : 115
% 0.20/0.42  # Proof object formula steps           : 60
% 0.20/0.42  # Proof object conjectures             : 68
% 0.20/0.42  # Proof object clause conjectures      : 65
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 46
% 0.20/0.42  # Proof object initial formulas used   : 30
% 0.20/0.42  # Proof object generating inferences   : 57
% 0.20/0.42  # Proof object simplifying inferences  : 181
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 30
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 58
% 0.20/0.42  # Removed in clause preprocessing      : 3
% 0.20/0.42  # Initial clauses in saturation        : 55
% 0.20/0.42  # Processed clauses                    : 618
% 0.20/0.42  # ...of these trivial                  : 27
% 0.20/0.42  # ...subsumed                          : 258
% 0.20/0.42  # ...remaining for further processing  : 333
% 0.20/0.42  # Other redundant clauses eliminated   : 6
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 25
% 0.20/0.42  # Backward-rewritten                   : 74
% 0.20/0.42  # Generated clauses                    : 880
% 0.20/0.42  # ...of the previous two non-trivial   : 744
% 0.20/0.42  # Contextual simplify-reflections      : 31
% 0.20/0.42  # Paramodulations                      : 865
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 8
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 170
% 0.20/0.42  #    Positive orientable unit clauses  : 43
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 11
% 0.20/0.42  #    Non-unit-clauses                  : 116
% 0.20/0.42  # Current number of unprocessed clauses: 174
% 0.20/0.42  # ...number of literals in the above   : 961
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 159
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3828
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1234
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 138
% 0.20/0.42  # Unit Clause-clause subsumption calls : 1304
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 29
% 0.20/0.42  # BW rewrite match successes           : 22
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 21914
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.064 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.071 s
% 0.20/0.42  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
