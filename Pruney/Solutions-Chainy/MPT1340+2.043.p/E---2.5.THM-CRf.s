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
% DateTime   : Thu Dec  3 11:13:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  173 (12350 expanded)
%              Number of clauses        :  116 (4523 expanded)
%              Number of leaves         :   28 (3109 expanded)
%              Depth                    :   21
%              Number of atoms          :  583 (61518 expanded)
%              Number of equality atoms :  127 (8713 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(rc1_relset_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_xboole_0(X3)
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

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

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

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

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(reflexivity_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_funct_2(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(c_0_28,negated_conjecture,(
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

fof(c_0_29,negated_conjecture,
    ( l1_struct_0(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0)
    & v2_funct_1(esk4_0)
    & ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

fof(c_0_30,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_31,plain,(
    ! [X54] :
      ( ~ l1_struct_0(X54)
      | k2_struct_0(X54) = u1_struct_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k2_struct_0(esk3_0) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X55] :
      ( v2_struct_0(X55)
      | ~ l1_struct_0(X55)
      | ~ v1_xboole_0(k2_struct_0(X55)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk4_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_42,plain,(
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

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k2_struct_0(esk3_0) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_46,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_47,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_48,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_49,plain,(
    ! [X50,X51,X52] :
      ( ( k5_relat_1(X52,k2_funct_1(X52)) = k6_partfun1(X50)
        | X51 = k1_xboole_0
        | k2_relset_1(X50,X51,X52) != X51
        | ~ v2_funct_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( k5_relat_1(k2_funct_1(X52),X52) = k6_partfun1(X51)
        | X51 = k1_xboole_0
        | k2_relset_1(X50,X51,X52) != X51
        | ~ v2_funct_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_50,plain,(
    ! [X42] : k6_partfun1(X42) = k6_relat_1(X42) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_51,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_xboole_0(X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_xboole_0(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_54,plain,(
    ! [X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_55,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_56,plain,(
    ! [X17] :
      ( ( v1_relat_1(k2_funct_1(X17))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( v1_funct_1(k2_funct_1(X17))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_57,plain,(
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

cnf(c_0_58,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37])]),c_0_45])).

cnf(c_0_62,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_67,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_69,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_70,plain,(
    ! [X39,X40] :
      ( m1_subset_1(esk1_2(X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      & v1_xboole_0(esk1_2(X39,X40))
      & v1_relat_1(esk1_2(X39,X40))
      & v4_relat_1(esk1_2(X39,X40),X39)
      & v5_relat_1(esk1_2(X39,X40),X40) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).

fof(c_0_71,plain,(
    ! [X12,X13] :
      ( ( ~ v5_relat_1(X13,X12)
        | r1_tarski(k2_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k2_relat_1(X13),X12)
        | v5_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_73,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_74,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_75,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_76,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_34]),c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_78,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_79,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_64])])).

fof(c_0_80,plain,(
    ! [X18] :
      ( v1_relat_1(k6_relat_1(X18))
      & v2_funct_1(k6_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_81,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_36]),c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_84,plain,(
    ! [X47,X48,X49] :
      ( ( v1_funct_1(k2_funct_1(X49))
        | ~ v2_funct_1(X49)
        | k2_relset_1(X47,X48,X49) != X48
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( v1_funct_2(k2_funct_1(X49),X48,X47)
        | ~ v2_funct_1(X49)
        | k2_relset_1(X47,X48,X49) != X48
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( m1_subset_1(k2_funct_1(X49),k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v2_funct_1(X49)
        | k2_relset_1(X47,X48,X49) != X48
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_87,plain,
    ( v1_xboole_0(esk1_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_89,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_79])])).

fof(c_0_92,plain,(
    ! [X20,X21] :
      ( ( v2_funct_1(X21)
        | ~ v2_funct_1(k5_relat_1(X21,X20))
        | k2_relat_1(X21) != k1_relat_1(X20)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( v2_funct_1(X20)
        | ~ v2_funct_1(k5_relat_1(X21,X20))
        | k2_relat_1(X21) != k1_relat_1(X20)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_93,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk3_0)) = k5_relat_1(k2_funct_1(esk4_0),esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_34]),c_0_82]),c_0_59]),c_0_83]),c_0_60])])).

cnf(c_0_95,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),X1)
    | ~ v5_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_39]),c_0_79])])).

cnf(c_0_99,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_100,plain,(
    ! [X16] :
      ( ( k1_relat_1(X16) != k1_xboole_0
        | k2_relat_1(X16) = k1_xboole_0
        | ~ v1_relat_1(X16) )
      & ( k2_relat_1(X16) != k1_xboole_0
        | k1_relat_1(X16) = k1_xboole_0
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_101,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_102,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_104,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_105,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k5_relat_1(k2_funct_1(esk4_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_82]),c_0_59]),c_0_83]),c_0_60]),c_0_34])])).

cnf(c_0_107,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_96]),c_0_97])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))
    | ~ v5_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_98])).

cnf(c_0_109,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_96])).

cnf(c_0_110,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_111,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_74])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_102]),c_0_39]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_113,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk4_0))
    | k2_relat_1(k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_91]),c_0_60]),c_0_106]),c_0_79])])).

cnf(c_0_114,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_107])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_91]),c_0_39]),c_0_79])])).

fof(c_0_117,plain,(
    ! [X56,X57,X58] :
      ( ~ v1_funct_1(X58)
      | ~ v1_funct_2(X58,X56,X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | k2_relset_1(X56,X57,X58) != X57
      | ~ v2_funct_1(X58)
      | k2_tops_2(X56,X57,X58) = k2_funct_1(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_118,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))
    | ~ v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_39]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_119,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_112])).

cnf(c_0_120,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk4_0))
    | k2_relat_1(k2_funct_1(esk4_0)) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_74]),c_0_60]),c_0_79])])).

cnf(c_0_121,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_116]),c_0_96])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_124,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_125,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_126,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_127,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])])).

cnf(c_0_128,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_103]),c_0_64])])).

cnf(c_0_129,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_73]),c_0_91]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_131,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_82]),c_0_59]),c_0_83]),c_0_60]),c_0_34])])).

cnf(c_0_132,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_73]),c_0_74]),c_0_75])).

fof(c_0_133,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ v2_funct_1(X23)
      | k2_relat_1(X24) != k1_relat_1(X23)
      | k5_relat_1(X24,X23) != k6_relat_1(k2_relat_1(X23))
      | X24 = k2_funct_1(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

fof(c_0_134,plain,(
    ! [X19] :
      ( ( v1_relat_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v2_funct_1(X19) )
      & ( v1_funct_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v2_funct_1(X19) )
      & ( v2_funct_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v2_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_135,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_126,c_0_66])).

cnf(c_0_136,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_127]),c_0_119]),c_0_128])])).

cnf(c_0_137,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_138,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_124]),c_0_106])])).

cnf(c_0_139,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_91]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_140,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_133])).

cnf(c_0_141,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk2_0)) = k5_relat_1(esk4_0,k2_funct_1(esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_34]),c_0_82]),c_0_59]),c_0_83]),c_0_60])])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(esk4_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_136]),c_0_137]),c_0_106]),c_0_128])])).

cnf(c_0_144,negated_conjecture,
    ( v1_funct_2(k2_funct_1(k2_funct_1(esk4_0)),k1_relat_1(k2_funct_1(k2_funct_1(esk4_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_136]),c_0_137]),c_0_106]),c_0_128])])).

cnf(c_0_145,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_102]),c_0_74]),c_0_75])).

cnf(c_0_146,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_137])])).

cnf(c_0_147,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_102]),c_0_39]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_148,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(X1,k2_funct_1(X2)) != k6_relat_1(k1_relat_1(X2))
    | k1_relat_1(k2_funct_1(X2)) != k2_relat_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_73]),c_0_74]),c_0_75]),c_0_141])).

cnf(c_0_149,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk2_0)) = k5_relat_1(esk4_0,k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_142,c_0_130])).

cnf(c_0_150,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_102]),c_0_137]),c_0_106]),c_0_128])])).

cnf(c_0_151,negated_conjecture,
    ( v1_funct_2(k2_funct_1(k2_funct_1(esk4_0)),k2_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_102]),c_0_137]),c_0_106]),c_0_128])])).

cnf(c_0_152,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_33])])).

cnf(c_0_153,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k2_relat_1(k2_funct_1(esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_136]),c_0_106]),c_0_128])])).

cnf(c_0_154,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),k2_relat_1(k2_funct_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_39]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_155,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_146,c_0_147])])).

cnf(c_0_156,negated_conjecture,
    ( X1 = k2_funct_1(k2_funct_1(esk4_0))
    | k5_relat_1(X1,k2_funct_1(esk4_0)) != k5_relat_1(esk4_0,k2_funct_1(esk4_0))
    | k2_relat_1(X1) != u1_struct_0(esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_91]),c_0_149]),c_0_136]),c_0_83]),c_0_60]),c_0_79])])).

fof(c_0_157,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,X43,X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,X43,X44)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | r2_funct_2(X43,X44,X45,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).

cnf(c_0_158,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_73]),c_0_91]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_159,negated_conjecture,
    ( v1_funct_2(k2_funct_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_73]),c_0_91]),c_0_83]),c_0_60]),c_0_79])])).

cnf(c_0_160,negated_conjecture,
    ( v1_funct_1(k2_funct_1(k2_funct_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154]),c_0_137]),c_0_106])])).

cnf(c_0_161,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_112])])).

cnf(c_0_162,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_156]),c_0_39]),c_0_60]),c_0_79])])).

cnf(c_0_163,plain,
    ( r2_funct_2(X2,X3,X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_157])).

cnf(c_0_164,negated_conjecture,
    ( v1_partfun1(k2_funct_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_158]),c_0_159]),c_0_160])]),c_0_61])).

cnf(c_0_165,negated_conjecture,
    ( v4_relat_1(k2_funct_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_158])).

cnf(c_0_166,negated_conjecture,
    ( v1_relat_1(k2_funct_1(k2_funct_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_143]),c_0_64])])).

cnf(c_0_167,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_168,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,X1)
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_34]),c_0_59]),c_0_60])])).

cnf(c_0_169,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k2_funct_1(esk4_0))) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_164]),c_0_165]),c_0_166])])).

cnf(c_0_170,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_59]),c_0_60]),c_0_34])])).

cnf(c_0_171,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_169]),c_0_137]),c_0_106]),c_0_128])])).

cnf(c_0_172,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_33]),c_0_171]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.030 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t64_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 0.19/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.42  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.42  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.42  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.42  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.19/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.42  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.19/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.42  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.42  fof(rc1_relset_1, axiom, ![X1, X2]:?[X3]:((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_xboole_0(X3))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 0.19/0.42  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.42  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.42  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.42  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 0.19/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.42  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.19/0.42  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 0.19/0.42  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.19/0.42  fof(reflexivity_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_funct_2(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 0.19/0.42  fof(c_0_28, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3)))))), inference(assume_negation,[status(cth)],[t64_tops_2])).
% 0.19/0.42  fof(c_0_29, negated_conjecture, (l1_struct_0(esk2_0)&((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&((k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)&v2_funct_1(esk4_0))&~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.19/0.42  fof(c_0_30, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_relset_1(X31,X32,X33)=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.42  fof(c_0_31, plain, ![X54]:(~l1_struct_0(X54)|k2_struct_0(X54)=u1_struct_0(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_33, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_35, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (k2_struct_0(esk3_0)=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  fof(c_0_38, plain, ![X55]:(v2_struct_0(X55)|~l1_struct_0(X55)|~v1_xboole_0(k2_struct_0(X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (k2_relat_1(esk4_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.42  fof(c_0_40, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  fof(c_0_41, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.42  fof(c_0_42, plain, ![X34, X35, X36]:((v1_funct_1(X36)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_xboole_0(X35))&(v1_partfun1(X36,X34)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_xboole_0(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.42  cnf(c_0_43, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (k2_struct_0(esk3_0)=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_39])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  fof(c_0_46, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  fof(c_0_47, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.42  fof(c_0_48, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.42  fof(c_0_49, plain, ![X50, X51, X52]:((k5_relat_1(X52,k2_funct_1(X52))=k6_partfun1(X50)|X51=k1_xboole_0|(k2_relset_1(X50,X51,X52)!=X51|~v2_funct_1(X52))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&(k5_relat_1(k2_funct_1(X52),X52)=k6_partfun1(X51)|X51=k1_xboole_0|(k2_relset_1(X50,X51,X52)!=X51|~v2_funct_1(X52))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.19/0.42  fof(c_0_50, plain, ![X42]:k6_partfun1(X42)=k6_relat_1(X42), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.42  fof(c_0_51, plain, ![X28, X29, X30]:(~v1_xboole_0(X28)|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_xboole_0(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.19/0.42  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.42  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  fof(c_0_54, plain, ![X53]:(((v1_funct_1(X53)|(~v1_relat_1(X53)|~v1_funct_1(X53)))&(v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))|(~v1_relat_1(X53)|~v1_funct_1(X53))))&(m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))|(~v1_relat_1(X53)|~v1_funct_1(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.42  fof(c_0_55, plain, ![X22]:((k2_relat_1(X22)=k1_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_relat_1(X22)=k2_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.42  fof(c_0_56, plain, ![X17]:((v1_relat_1(k2_funct_1(X17))|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(v1_funct_1(k2_funct_1(X17))|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.42  fof(c_0_57, plain, ![X37, X38]:((~v1_partfun1(X38,X37)|k1_relat_1(X38)=X37|(~v1_relat_1(X38)|~v4_relat_1(X38,X37)))&(k1_relat_1(X38)!=X37|v1_partfun1(X38,X37)|(~v1_relat_1(X38)|~v4_relat_1(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.42  cnf(c_0_58, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_37])]), c_0_45])).
% 0.19/0.42  cnf(c_0_62, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_63, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_64, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_65, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.42  cnf(c_0_66, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  fof(c_0_67, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_68, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_69, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.42  fof(c_0_70, plain, ![X39, X40]:((((m1_subset_1(esk1_2(X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X40)))&v1_xboole_0(esk1_2(X39,X40)))&v1_relat_1(esk1_2(X39,X40)))&v4_relat_1(esk1_2(X39,X40),X39))&v5_relat_1(esk1_2(X39,X40),X40)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).
% 0.19/0.42  fof(c_0_71, plain, ![X12, X13]:((~v5_relat_1(X13,X12)|r1_tarski(k2_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k2_relat_1(X13),X12)|v5_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.42  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.42  cnf(c_0_73, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_74, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.42  cnf(c_0_75, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.42  cnf(c_0_76, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_34]), c_0_59]), c_0_60])]), c_0_61])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_34])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_64])])).
% 0.19/0.42  fof(c_0_80, plain, ![X18]:(v1_relat_1(k6_relat_1(X18))&v2_funct_1(k6_relat_1(X18))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.42  cnf(c_0_81, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_36]), c_0_39])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  fof(c_0_84, plain, ![X47, X48, X49]:(((v1_funct_1(k2_funct_1(X49))|(~v2_funct_1(X49)|k2_relset_1(X47,X48,X49)!=X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(v1_funct_2(k2_funct_1(X49),X48,X47)|(~v2_funct_1(X49)|k2_relset_1(X47,X48,X49)!=X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))))&(m1_subset_1(k2_funct_1(X49),k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|(~v2_funct_1(X49)|k2_relset_1(X47,X48,X49)!=X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.42  cnf(c_0_85, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.42  cnf(c_0_86, plain, (v1_xboole_0(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.42  cnf(c_0_87, plain, (v1_xboole_0(esk1_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.42  cnf(c_0_88, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.42  cnf(c_0_89, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.42  cnf(c_0_90, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_79])])).
% 0.19/0.42  fof(c_0_92, plain, ![X20, X21]:((v2_funct_1(X21)|(~v2_funct_1(k5_relat_1(X21,X20))|k2_relat_1(X21)!=k1_relat_1(X20))|(~v1_relat_1(X21)|~v1_funct_1(X21))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(v2_funct_1(X20)|(~v2_funct_1(k5_relat_1(X21,X20))|k2_relat_1(X21)!=k1_relat_1(X20))|(~v1_relat_1(X21)|~v1_funct_1(X21))|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 0.19/0.42  cnf(c_0_93, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (k6_relat_1(u1_struct_0(esk3_0))=k5_relat_1(k2_funct_1(esk4_0),esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_34]), c_0_82]), c_0_59]), c_0_83]), c_0_60])])).
% 0.19/0.42  cnf(c_0_95, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.42  cnf(c_0_96, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_85])).
% 0.19/0.42  cnf(c_0_97, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.42  cnf(c_0_98, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),X1)|~v5_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_39]), c_0_79])])).
% 0.19/0.42  cnf(c_0_99, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  fof(c_0_100, plain, ![X16]:((k1_relat_1(X16)!=k1_xboole_0|k2_relat_1(X16)=k1_xboole_0|~v1_relat_1(X16))&(k2_relat_1(X16)!=k1_xboole_0|k1_relat_1(X16)=k1_xboole_0|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.42  cnf(c_0_101, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_89])).
% 0.19/0.42  cnf(c_0_102, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_103, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_104, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,X2))|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.19/0.42  cnf(c_0_105, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k5_relat_1(k2_funct_1(esk4_0),esk4_0))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.42  cnf(c_0_106, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_82]), c_0_59]), c_0_83]), c_0_60]), c_0_34])])).
% 0.19/0.42  cnf(c_0_107, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_96]), c_0_97])])).
% 0.19/0.42  cnf(c_0_108, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))|~v5_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_98])).
% 0.19/0.42  cnf(c_0_109, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_99, c_0_96])).
% 0.19/0.42  cnf(c_0_110, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.42  cnf(c_0_111, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_74])).
% 0.19/0.42  cnf(c_0_112, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_102]), c_0_39]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_113, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk4_0))|k2_relat_1(k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_91]), c_0_60]), c_0_106]), c_0_79])])).
% 0.19/0.42  cnf(c_0_114, negated_conjecture, (~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_61, c_0_107])).
% 0.19/0.42  cnf(c_0_115, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.19/0.42  cnf(c_0_116, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_91]), c_0_39]), c_0_79])])).
% 0.19/0.42  fof(c_0_117, plain, ![X56, X57, X58]:(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|(k2_relset_1(X56,X57,X58)!=X57|~v2_funct_1(X58)|k2_tops_2(X56,X57,X58)=k2_funct_1(X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.19/0.42  cnf(c_0_118, negated_conjecture, (v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))|~v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_39]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_119, negated_conjecture, (v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_112])).
% 0.19/0.42  cnf(c_0_120, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk4_0))|k2_relat_1(k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_74]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_121, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.19/0.42  cnf(c_0_122, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_116]), c_0_96])).
% 0.19/0.42  cnf(c_0_123, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_124, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.19/0.42  cnf(c_0_125, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.42  cnf(c_0_126, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.42  cnf(c_0_127, negated_conjecture, (v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])])).
% 0.19/0.42  cnf(c_0_128, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_103]), c_0_64])])).
% 0.19/0.42  cnf(c_0_129, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_73]), c_0_91]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_130, negated_conjecture, (u1_struct_0(esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.19/0.42  cnf(c_0_131, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_82]), c_0_59]), c_0_83]), c_0_60]), c_0_34])])).
% 0.19/0.42  cnf(c_0_132, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_73]), c_0_74]), c_0_75])).
% 0.19/0.42  fof(c_0_133, plain, ![X23, X24]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v1_relat_1(X24)|~v1_funct_1(X24)|(~v2_funct_1(X23)|k2_relat_1(X24)!=k1_relat_1(X23)|k5_relat_1(X24,X23)!=k6_relat_1(k2_relat_1(X23))|X24=k2_funct_1(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.19/0.42  fof(c_0_134, plain, ![X19]:(((v1_relat_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)|~v2_funct_1(X19)))&(v1_funct_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)|~v2_funct_1(X19))))&(v2_funct_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)|~v2_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.19/0.42  cnf(c_0_135, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_126, c_0_66])).
% 0.19/0.42  cnf(c_0_136, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_127]), c_0_119]), c_0_128])])).
% 0.19/0.42  cnf(c_0_137, negated_conjecture, (v2_funct_1(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[c_0_129, c_0_130])).
% 0.19/0.42  cnf(c_0_138, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_124]), c_0_106])])).
% 0.19/0.42  cnf(c_0_139, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_91]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_140, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_133])).
% 0.19/0.42  cnf(c_0_141, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_134])).
% 0.19/0.42  cnf(c_0_142, negated_conjecture, (k6_relat_1(u1_struct_0(esk2_0))=k5_relat_1(esk4_0,k2_funct_1(esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_34]), c_0_82]), c_0_59]), c_0_83]), c_0_60])])).
% 0.19/0.42  cnf(c_0_143, negated_conjecture, (m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(esk4_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_136]), c_0_137]), c_0_106]), c_0_128])])).
% 0.19/0.42  cnf(c_0_144, negated_conjecture, (v1_funct_2(k2_funct_1(k2_funct_1(esk4_0)),k1_relat_1(k2_funct_1(k2_funct_1(esk4_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_136]), c_0_137]), c_0_106]), c_0_128])])).
% 0.19/0.42  cnf(c_0_145, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_102]), c_0_74]), c_0_75])).
% 0.19/0.42  cnf(c_0_146, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_137])])).
% 0.19/0.42  cnf(c_0_147, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_102]), c_0_39]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_148, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(X1,k2_funct_1(X2))!=k6_relat_1(k1_relat_1(X2))|k1_relat_1(k2_funct_1(X2))!=k2_relat_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_73]), c_0_74]), c_0_75]), c_0_141])).
% 0.19/0.42  cnf(c_0_149, negated_conjecture, (k6_relat_1(u1_struct_0(esk2_0))=k5_relat_1(esk4_0,k2_funct_1(esk4_0))), inference(sr,[status(thm)],[c_0_142, c_0_130])).
% 0.19/0.42  cnf(c_0_150, negated_conjecture, (m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_102]), c_0_137]), c_0_106]), c_0_128])])).
% 0.19/0.42  cnf(c_0_151, negated_conjecture, (v1_funct_2(k2_funct_1(k2_funct_1(esk4_0)),k2_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_102]), c_0_137]), c_0_106]), c_0_128])])).
% 0.19/0.42  cnf(c_0_152, plain, (v1_funct_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_33])])).
% 0.19/0.42  cnf(c_0_153, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k2_relat_1(k2_funct_1(esk4_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_136]), c_0_106]), c_0_128])])).
% 0.19/0.42  cnf(c_0_154, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),k2_relat_1(k2_funct_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_39]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_155, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_146, c_0_147])])).
% 0.19/0.42  cnf(c_0_156, negated_conjecture, (X1=k2_funct_1(k2_funct_1(esk4_0))|k5_relat_1(X1,k2_funct_1(esk4_0))!=k5_relat_1(esk4_0,k2_funct_1(esk4_0))|k2_relat_1(X1)!=u1_struct_0(esk3_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_91]), c_0_149]), c_0_136]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  fof(c_0_157, plain, ![X43, X44, X45, X46]:(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|~v1_funct_1(X46)|~v1_funct_2(X46,X43,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|r2_funct_2(X43,X44,X45,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).
% 0.19/0.42  cnf(c_0_158, negated_conjecture, (m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_73]), c_0_91]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_159, negated_conjecture, (v1_funct_2(k2_funct_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_73]), c_0_91]), c_0_83]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_160, negated_conjecture, (v1_funct_1(k2_funct_1(k2_funct_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154]), c_0_137]), c_0_106])])).
% 0.19/0.42  cnf(c_0_161, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_155, c_0_112])])).
% 0.19/0.42  cnf(c_0_162, negated_conjecture, (k2_funct_1(k2_funct_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_156]), c_0_39]), c_0_60]), c_0_79])])).
% 0.19/0.42  cnf(c_0_163, plain, (r2_funct_2(X2,X3,X1,X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_157])).
% 0.19/0.42  cnf(c_0_164, negated_conjecture, (v1_partfun1(k2_funct_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_158]), c_0_159]), c_0_160])]), c_0_61])).
% 0.19/0.42  cnf(c_0_165, negated_conjecture, (v4_relat_1(k2_funct_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_158])).
% 0.19/0.42  cnf(c_0_166, negated_conjecture, (v1_relat_1(k2_funct_1(k2_funct_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_143]), c_0_64])])).
% 0.19/0.42  cnf(c_0_167, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_161, c_0_162])).
% 0.19/0.42  cnf(c_0_168, negated_conjecture, (r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,X1)|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_34]), c_0_59]), c_0_60])])).
% 0.19/0.42  cnf(c_0_169, negated_conjecture, (k1_relat_1(k2_funct_1(k2_funct_1(esk4_0)))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_164]), c_0_165]), c_0_166])])).
% 0.19/0.42  cnf(c_0_170, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_59]), c_0_60]), c_0_34])])).
% 0.19/0.42  cnf(c_0_171, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_169]), c_0_137]), c_0_106]), c_0_128])])).
% 0.19/0.42  cnf(c_0_172, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_33]), c_0_171]), c_0_112])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 173
% 0.19/0.42  # Proof object clause steps            : 116
% 0.19/0.42  # Proof object formula steps           : 57
% 0.19/0.42  # Proof object conjectures             : 71
% 0.19/0.42  # Proof object clause conjectures      : 68
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 41
% 0.19/0.42  # Proof object initial formulas used   : 28
% 0.19/0.42  # Proof object generating inferences   : 62
% 0.19/0.42  # Proof object simplifying inferences  : 186
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 28
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 59
% 0.19/0.42  # Removed in clause preprocessing      : 3
% 0.19/0.42  # Initial clauses in saturation        : 56
% 0.19/0.42  # Processed clauses                    : 641
% 0.19/0.42  # ...of these trivial                  : 14
% 0.19/0.42  # ...subsumed                          : 215
% 0.19/0.42  # ...remaining for further processing  : 412
% 0.19/0.42  # Other redundant clauses eliminated   : 6
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 13
% 0.19/0.42  # Backward-rewritten                   : 118
% 0.19/0.42  # Generated clauses                    : 1191
% 0.19/0.42  # ...of the previous two non-trivial   : 1075
% 0.19/0.42  # Contextual simplify-reflections      : 22
% 0.19/0.42  # Paramodulations                      : 1176
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 9
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 218
% 0.19/0.42  #    Positive orientable unit clauses  : 83
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 9
% 0.19/0.42  #    Non-unit-clauses                  : 126
% 0.19/0.42  # Current number of unprocessed clauses: 416
% 0.19/0.42  # ...number of literals in the above   : 2336
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 192
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 5006
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 1885
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 145
% 0.19/0.42  # Unit Clause-clause subsumption calls : 745
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 71
% 0.19/0.42  # BW rewrite match successes           : 30
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 27521
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.075 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.081 s
% 0.19/0.42  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
