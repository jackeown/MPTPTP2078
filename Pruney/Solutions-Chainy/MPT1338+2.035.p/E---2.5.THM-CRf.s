%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 313 expanded)
%              Number of clauses        :   66 ( 116 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  345 (1717 expanded)
%              Number of equality atoms :  121 ( 531 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_tops_2,conjecture,(
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
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(rc20_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v1_zfmisc_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(c_0_23,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_tops_2])).

fof(c_0_24,plain,(
    ! [X50,X51,X52] :
      ( ~ v1_funct_1(X52)
      | ~ v1_funct_2(X52,X50,X51)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k2_relset_1(X50,X51,X52) != X51
      | ~ v2_funct_1(X52)
      | k2_tops_2(X50,X51,X52) = k2_funct_1(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

fof(c_0_25,negated_conjecture,
    ( l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    & k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0) = k2_struct_0(esk6_0)
    & v2_funct_1(esk7_0)
    & ( k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)) != k2_struct_0(esk6_0)
      | k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)) != k2_struct_0(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_26,plain,(
    ! [X40,X41,X42] :
      ( ( v1_funct_1(k2_funct_1(X42))
        | ~ v2_funct_1(X42)
        | k2_relset_1(X40,X41,X42) != X41
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v1_funct_2(k2_funct_1(X42),X41,X40)
        | ~ v2_funct_1(X42)
        | k2_relset_1(X40,X41,X42) != X41
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( m1_subset_1(k2_funct_1(X42),k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | ~ v2_funct_1(X42)
        | k2_relset_1(X40,X41,X42) != X41
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_27,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0) = k2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X43] :
      ( ~ l1_struct_0(X43)
      | k2_struct_0(X43) = u1_struct_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0) = k2_funct_1(esk7_0)
    | k2_struct_0(esk6_0) != u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_36,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))
    | k2_struct_0(esk6_0) != u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_40,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)) != k2_struct_0(esk6_0)
    | k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)) != k2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0) = k2_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_36]),c_0_37])])).

fof(c_0_44,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_45,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_46,plain,(
    ! [X22,X23] :
      ( ( ~ r1_tarski(X23,k3_subset_1(X22,X23))
        | X23 = k1_subset_1(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(X22)) )
      & ( X23 != k1_subset_1(X22)
        | r1_tarski(X23,k3_subset_1(X22,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_47,plain,(
    ! [X15] : k1_subset_1(X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_48,plain,(
    ! [X21] : k2_subset_1(X21) = k3_subset_1(X21,k1_subset_1(X21)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_49,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_50,plain,(
    ! [X17] : m1_subset_1(k1_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

cnf(c_0_51,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0)) != k2_struct_0(esk6_0)
    | k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0)) != k2_struct_0(esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0)) = k1_relat_1(k2_funct_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_53,plain,(
    ! [X27] :
      ( ( k2_relat_1(X27) = k1_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k1_relat_1(X27) = k2_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_54,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_56,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_57,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | r1_tarski(X7,X5)
        | X6 != k1_zfmisc_1(X5) )
      & ( ~ r1_tarski(X8,X5)
        | r2_hidden(X8,X6)
        | X6 != k1_zfmisc_1(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | ~ r1_tarski(esk1_2(X9,X10),X9)
        | X10 = k1_zfmisc_1(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(esk1_2(X9,X10),X9)
        | X10 = k1_zfmisc_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X1))
    | X1 != k1_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0)) != k2_struct_0(esk5_0)
    | k1_relat_1(k2_funct_1(esk7_0)) != k2_struct_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k2_relat_1(esk7_0) = k2_struct_0(esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_32])).

fof(c_0_67,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_68,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X1))
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_59])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0)) != k2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_30]),c_0_31]),c_0_66])])).

cnf(c_0_74,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0)) = k2_relat_1(k2_funct_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_43])).

fof(c_0_75,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X39 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != k1_xboole_0
        | v1_funct_2(X39,X37,X38)
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_61])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_71]),c_0_72])])).

cnf(c_0_80,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk7_0)) != k2_struct_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_82,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

fof(c_0_84,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_85,plain,(
    ! [X44] :
      ( ( m1_subset_1(esk3_1(X44),k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ l1_struct_0(X44) )
      & ( ~ v1_xboole_0(esk3_1(X44))
        | v2_struct_0(X44)
        | ~ l1_struct_0(X44) )
      & ( v1_zfmisc_1(esk3_1(X44))
        | v2_struct_0(X44)
        | ~ l1_struct_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc20_struct_0])])])])])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(esk7_0) != k2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_30]),c_0_31]),c_0_66])])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk7_0) = u1_struct_0(esk5_0)
    | u1_struct_0(esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_32]),c_0_29])]),c_0_83])).

fof(c_0_90,plain,(
    ! [X46,X47,X48] :
      ( ( X47 = k1_xboole_0
        | ~ r2_hidden(X47,X46)
        | k3_tarski(X46) != k1_xboole_0 )
      & ( esk4_1(X48) != k1_xboole_0
        | k3_tarski(X48) = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X48),X48)
        | k3_tarski(X48) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_91,plain,(
    ! [X12] : k3_tarski(k1_zfmisc_1(X12)) = X12 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_94,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk6_0) = k1_xboole_0
    | k2_struct_0(esk5_0) != u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_97,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_98,plain,(
    ! [X19] :
      ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(X19))
      & v1_xboole_0(esk2_1(X19)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_100,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_101,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( u1_struct_0(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_36]),c_0_96])])).

cnf(c_0_103,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_104,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_105,plain,
    ( v1_xboole_0(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_37])]),c_0_103])).

cnf(c_0_108,plain,
    ( esk2_1(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk3_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_110,negated_conjecture,
    ( esk3_1(esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_37]),c_0_111])]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.39  # and selection function SelectNewComplexAHPNS.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t62_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 0.19/0.39  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 0.19/0.39  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.39  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.19/0.39  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.39  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.19/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.39  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.19/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.39  fof(rc20_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc20_struct_0)).
% 0.19/0.39  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.19/0.39  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.39  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.19/0.39  fof(c_0_23, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t62_tops_2])).
% 0.19/0.39  fof(c_0_24, plain, ![X50, X51, X52]:(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|(k2_relset_1(X50,X51,X52)!=X51|~v2_funct_1(X52)|k2_tops_2(X50,X51,X52)=k2_funct_1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.19/0.39  fof(c_0_25, negated_conjecture, (l1_struct_0(esk5_0)&((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))))&((k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)=k2_struct_0(esk6_0)&v2_funct_1(esk7_0))&(k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0))!=k2_struct_0(esk6_0)|k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0))!=k2_struct_0(esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.19/0.39  fof(c_0_26, plain, ![X40, X41, X42]:(((v1_funct_1(k2_funct_1(X42))|(~v2_funct_1(X42)|k2_relset_1(X40,X41,X42)!=X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&(v1_funct_2(k2_funct_1(X42),X41,X40)|(~v2_funct_1(X42)|k2_relset_1(X40,X41,X42)!=X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))))&(m1_subset_1(k2_funct_1(X42),k1_zfmisc_1(k2_zfmisc_1(X41,X40)))|(~v2_funct_1(X42)|k2_relset_1(X40,X41,X42)!=X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.39  cnf(c_0_27, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)=k2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  fof(c_0_33, plain, ![X43]:(~l1_struct_0(X43)|k2_struct_0(X43)=u1_struct_0(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.39  cnf(c_0_34, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)=k2_funct_1(esk7_0)|k2_struct_0(esk6_0)!=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])])).
% 0.19/0.39  cnf(c_0_36, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  fof(c_0_38, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))|k2_struct_0(esk6_0)!=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0))!=k2_struct_0(esk6_0)|k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0))!=k2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (k2_tops_2(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)=k2_funct_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.39  cnf(c_0_42, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_36]), c_0_37])])).
% 0.19/0.39  fof(c_0_44, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.39  fof(c_0_45, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.39  fof(c_0_46, plain, ![X22, X23]:((~r1_tarski(X23,k3_subset_1(X22,X23))|X23=k1_subset_1(X22)|~m1_subset_1(X23,k1_zfmisc_1(X22)))&(X23!=k1_subset_1(X22)|r1_tarski(X23,k3_subset_1(X22,X23))|~m1_subset_1(X23,k1_zfmisc_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.19/0.39  fof(c_0_47, plain, ![X15]:k1_subset_1(X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.39  fof(c_0_48, plain, ![X21]:k2_subset_1(X21)=k3_subset_1(X21,k1_subset_1(X21)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.19/0.39  fof(c_0_49, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.39  fof(c_0_50, plain, ![X17]:m1_subset_1(k1_subset_1(X17),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0))!=k2_struct_0(esk6_0)|k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0))!=k2_struct_0(esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0))=k1_relat_1(k2_funct_1(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.39  fof(c_0_53, plain, ![X27]:((k2_relat_1(X27)=k1_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(k1_relat_1(X27)=k2_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.39  cnf(c_0_54, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.39  cnf(c_0_55, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  fof(c_0_56, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.39  fof(c_0_57, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|r1_tarski(X7,X5)|X6!=k1_zfmisc_1(X5))&(~r1_tarski(X8,X5)|r2_hidden(X8,X6)|X6!=k1_zfmisc_1(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|~r1_tarski(esk1_2(X9,X10),X9)|X10=k1_zfmisc_1(X9))&(r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(esk1_2(X9,X10),X9)|X10=k1_zfmisc_1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.39  cnf(c_0_58, plain, (r1_tarski(X1,k3_subset_1(X2,X1))|X1!=k1_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_59, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_60, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_61, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.39  cnf(c_0_62, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0))!=k2_struct_0(esk5_0)|k1_relat_1(k2_funct_1(esk7_0))!=k2_struct_0(esk6_0)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.39  cnf(c_0_64, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (k2_relat_1(esk7_0)=k2_struct_0(esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_32]), c_0_28])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_55, c_0_32])).
% 0.19/0.39  fof(c_0_67, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.39  cnf(c_0_68, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.39  cnf(c_0_69, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.39  cnf(c_0_70, plain, (r1_tarski(X1,k3_subset_1(X2,X1))|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.39  cnf(c_0_71, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_59])).
% 0.19/0.39  cnf(c_0_72, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_62, c_0_59])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0))!=k2_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_30]), c_0_31]), c_0_66])])).
% 0.19/0.39  cnf(c_0_74, negated_conjecture, (k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_funct_1(esk7_0))=k2_relat_1(k2_funct_1(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_43])).
% 0.19/0.39  fof(c_0_75, plain, ![X37, X38, X39]:((((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))&((~v1_funct_2(X39,X37,X38)|X39=k1_xboole_0|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X39!=k1_xboole_0|v1_funct_2(X39,X37,X38)|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.39  cnf(c_0_76, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.39  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_68, c_0_61])).
% 0.19/0.39  cnf(c_0_78, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_69])).
% 0.19/0.39  cnf(c_0_79, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_71]), c_0_72])])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (k2_relat_1(k2_funct_1(esk7_0))!=k2_struct_0(esk5_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.39  cnf(c_0_81, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.39  cnf(c_0_82, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_42, c_0_32])).
% 0.19/0.39  fof(c_0_84, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.39  fof(c_0_85, plain, ![X44]:(((m1_subset_1(esk3_1(X44),k1_zfmisc_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~l1_struct_0(X44)))&(~v1_xboole_0(esk3_1(X44))|(v2_struct_0(X44)|~l1_struct_0(X44))))&(v1_zfmisc_1(esk3_1(X44))|(v2_struct_0(X44)|~l1_struct_0(X44)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc20_struct_0])])])])])).
% 0.19/0.39  cnf(c_0_86, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.39  cnf(c_0_87, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.39  cnf(c_0_88, negated_conjecture, (k1_relat_1(esk7_0)!=k2_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_30]), c_0_31]), c_0_66])])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (k1_relat_1(esk7_0)=u1_struct_0(esk5_0)|u1_struct_0(esk6_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_32]), c_0_29])]), c_0_83])).
% 0.19/0.39  fof(c_0_90, plain, ![X46, X47, X48]:((X47=k1_xboole_0|~r2_hidden(X47,X46)|k3_tarski(X46)!=k1_xboole_0)&((esk4_1(X48)!=k1_xboole_0|k3_tarski(X48)=k1_xboole_0)&(r2_hidden(esk4_1(X48),X48)|k3_tarski(X48)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.19/0.39  fof(c_0_91, plain, ![X12]:k3_tarski(k1_zfmisc_1(X12))=X12, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.39  cnf(c_0_92, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.39  cnf(c_0_93, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.39  cnf(c_0_94, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.39  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk6_0)=k1_xboole_0|k2_struct_0(esk5_0)!=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.39  cnf(c_0_96, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  fof(c_0_97, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.39  fof(c_0_98, plain, ![X19]:(m1_subset_1(esk2_1(X19),k1_zfmisc_1(X19))&v1_xboole_0(esk2_1(X19))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.19/0.39  cnf(c_0_99, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.39  cnf(c_0_100, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.39  cnf(c_0_101, plain, (v2_struct_0(X1)|r2_hidden(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.19/0.39  cnf(c_0_102, negated_conjecture, (u1_struct_0(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_36]), c_0_96])])).
% 0.19/0.39  cnf(c_0_103, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_104, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.39  cnf(c_0_105, plain, (v1_xboole_0(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.39  cnf(c_0_106, plain, (X1=k1_xboole_0|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100])])).
% 0.19/0.39  cnf(c_0_107, negated_conjecture, (r2_hidden(esk3_1(esk6_0),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_37])]), c_0_103])).
% 0.19/0.39  cnf(c_0_108, plain, (esk2_1(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.19/0.39  cnf(c_0_109, plain, (v2_struct_0(X1)|~v1_xboole_0(esk3_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.39  cnf(c_0_110, negated_conjecture, (esk3_1(esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.19/0.39  cnf(c_0_111, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_105, c_0_108])).
% 0.19/0.39  cnf(c_0_112, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_37]), c_0_111])]), c_0_103]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 113
% 0.19/0.39  # Proof object clause steps            : 66
% 0.19/0.39  # Proof object formula steps           : 47
% 0.19/0.39  # Proof object conjectures             : 32
% 0.19/0.39  # Proof object clause conjectures      : 29
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 33
% 0.19/0.39  # Proof object initial formulas used   : 23
% 0.19/0.39  # Proof object generating inferences   : 23
% 0.19/0.39  # Proof object simplifying inferences  : 53
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 23
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 51
% 0.19/0.39  # Removed in clause preprocessing      : 2
% 0.19/0.39  # Initial clauses in saturation        : 49
% 0.19/0.39  # Processed clauses                    : 222
% 0.19/0.39  # ...of these trivial                  : 2
% 0.19/0.39  # ...subsumed                          : 35
% 0.19/0.39  # ...remaining for further processing  : 185
% 0.19/0.39  # Other redundant clauses eliminated   : 24
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 34
% 0.19/0.39  # Generated clauses                    : 227
% 0.19/0.39  # ...of the previous two non-trivial   : 208
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 204
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 24
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 94
% 0.19/0.39  #    Positive orientable unit clauses  : 30
% 0.19/0.39  #    Positive unorientable unit clauses: 6
% 0.19/0.39  #    Negative unit clauses             : 4
% 0.19/0.39  #    Non-unit-clauses                  : 54
% 0.19/0.39  # Current number of unprocessed clauses: 75
% 0.19/0.39  # ...number of literals in the above   : 208
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 86
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1087
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 440
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.19/0.39  # Unit Clause-clause subsumption calls : 438
% 0.19/0.39  # Rewrite failures with RHS unbound    : 36
% 0.19/0.39  # BW rewrite match attempts            : 72
% 0.19/0.39  # BW rewrite match successes           : 14
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 6928
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.041 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.045 s
% 0.19/0.39  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
