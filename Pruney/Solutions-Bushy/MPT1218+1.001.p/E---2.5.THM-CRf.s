%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1218+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:55 EST 2020

% Result     : Theorem 13.44s
% Output     : CNFRefutation 13.44s
% Verified   : 
% Statistics : Number of formulae       :  134 (2704 expanded)
%              Number of clauses        :   96 (1031 expanded)
%              Number of leaves         :   19 ( 669 expanded)
%              Depth                    :   22
%              Number of atoms          :  570 (14332 expanded)
%              Number of equality atoms :   31 (1290 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v18_lattices(X2,X1)
            & v19_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => X2 = k2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_lattices)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_l1_lattices,axiom,(
    ! [X1] :
      ( l1_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(t23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(d22_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v18_lattices(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r3_lattices(X1,X3,X4)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattices)).

fof(d23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v19_lattices(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r3_lattices(X1,X3,X4)
                        & r2_hidden(X3,X2) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d23_lattices)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v18_lattices(X2,X1)
              & v19_lattices(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => X2 = k2_struct_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t54_lattices])).

fof(c_0_20,plain,(
    ! [X45,X46,X47] :
      ( ( m1_subset_1(esk6_3(X45,X46,X47),X45)
        | X46 = X47
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( ~ r2_hidden(esk6_3(X45,X46,X47),X46)
        | ~ r2_hidden(esk6_3(X45,X46,X47),X47)
        | X46 = X47
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( r2_hidden(esk6_3(X45,X46,X47),X46)
        | r2_hidden(esk6_3(X45,X46,X47),X47)
        | X46 = X47
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & l3_lattices(esk7_0)
    & ~ v1_xboole_0(esk8_0)
    & v18_lattices(esk8_0,esk7_0)
    & v19_lattices(esk8_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & esk8_0 != k2_struct_0(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X22] :
      ( ~ l1_struct_0(X22)
      | m1_subset_1(k2_struct_0(X22),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk8_0
    | m1_subset_1(esk6_3(u1_struct_0(esk7_0),X1,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk8_0 != k2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X26] :
      ( ~ l1_lattices(X26)
      | l1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_lattices])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_31,plain,(
    ! [X27] :
      ( ( l1_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( l2_lattices(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_32,plain,(
    ! [X38,X39,X40] :
      ( ~ r2_hidden(X38,X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(X40))
      | m1_subset_1(X38,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_34,plain,(
    ! [X28] : m1_subset_1(esk5_1(X28),X28) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_35,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v6_lattices(X23)
      | ~ l1_lattices(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | m1_subset_1(k4_lattices(X23,X24,X25),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_45,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_lattices(X30,X31,X32)
        | r1_lattices(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v6_lattices(X30)
        | ~ v8_lattices(X30)
        | ~ v9_lattices(X30)
        | ~ l3_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) )
      & ( ~ r1_lattices(X30,X31,X32)
        | r3_lattices(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v6_lattices(X30)
        | ~ v8_lattices(X30)
        | ~ v9_lattices(X30)
        | ~ l3_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_49,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v6_lattices(X33)
      | ~ v8_lattices(X33)
      | ~ l3_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | r1_lattices(X33,k4_lattices(X33,X34,X35),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

fof(c_0_50,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v6_lattices(X6)
      | ~ l1_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k4_lattices(X6,X7,X8) = k4_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

fof(c_0_52,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_53,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk5_1(esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v18_lattices(X10,X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r3_lattices(X9,X11,X12)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X11,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_2(X9,X10),u1_struct_0(X9))
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( r3_lattices(X9,esk1_2(X9,X10),esk2_2(X9,X10))
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( r2_hidden(esk2_2(X9,X10),X10)
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattices])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_38])])).

cnf(c_0_59,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38])]),c_0_44])).

cnf(c_0_62,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_38])]),c_0_44])).

cnf(c_0_64,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( k4_lattices(esk7_0,X1,esk5_1(esk8_0)) = k4_lattices(esk7_0,esk5_1(esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_44])).

fof(c_0_66,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ v19_lattices(X16,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r3_lattices(X15,X17,X18)
        | ~ r2_hidden(X17,X16)
        | r2_hidden(X18,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk3_2(X15,X16),u1_struct_0(X15))
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_2(X15,X16),u1_struct_0(X15))
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( r3_lattices(X15,esk3_2(X15,X16),esk4_2(X15,X16))
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d23_lattices])])])])])])).

cnf(c_0_67,plain,
    ( r2_hidden(X3,X1)
    | v2_struct_0(X2)
    | ~ v18_lattices(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X3,X4)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_71,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_38])]),c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk5_1(esk8_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_38])]),c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( k4_lattices(esk7_0,X1,esk5_1(esk8_0)) = k4_lattices(esk7_0,esk5_1(esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_37]),c_0_38])])).

cnf(c_0_74,plain,
    ( X2 = X3
    | ~ r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_75,plain,
    ( r2_hidden(X4,X1)
    | v2_struct_0(X2)
    | ~ v19_lattices(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X3,X4)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X4,X2)
    | ~ r3_lattices(X3,X1,X4)
    | ~ v18_lattices(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_67,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_64]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_59]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_62]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk5_1(esk8_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_64]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( k4_lattices(esk7_0,X1,esk5_1(esk8_0)) = k4_lattices(esk7_0,esk5_1(esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_59]),c_0_60]),c_0_38])]),c_0_44])).

fof(c_0_83,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | ~ v1_xboole_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_84,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),X1,esk8_0),esk8_0)
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),X1,esk8_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_23])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ v19_lattices(X2,X3)
    | ~ r2_hidden(X4,X2)
    | ~ r3_lattices(X3,X4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_75,c_0_39])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r3_lattices(esk7_0,k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),X2)
    | ~ v18_lattices(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_87,negated_conjecture,
    ( v18_lattices(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk5_1(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_59]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_89,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),esk5_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_54])).

cnf(c_0_90,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_64]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_91,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,X1,esk5_1(esk8_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_59]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_92,negated_conjecture,
    ( k4_lattices(esk7_0,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),esk5_1(esk8_0)) = k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_43])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( ~ l1_struct_0(esk7_0)
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),k2_struct_0(esk7_0))
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_26]),c_0_27])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),X1)
    | ~ v19_lattices(X1,esk7_0)
    | ~ r2_hidden(X2,X1)
    | ~ r3_lattices(esk7_0,X2,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_43]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_96,negated_conjecture,
    ( v19_lattices(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),esk8_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ r3_lattices(esk7_0,k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_23])])).

cnf(c_0_98,negated_conjecture,
    ( r3_lattices(esk7_0,k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),esk5_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_77]),c_0_89])])).

cnf(c_0_99,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_59]),c_0_60]),c_0_38])]),c_0_44])).

cnf(c_0_100,negated_conjecture,
    ( r1_lattices(esk7_0,k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_43]),c_0_92])).

fof(c_0_101,plain,(
    ! [X44] :
      ( ~ v1_xboole_0(X44)
      | X44 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_102,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_41])).

fof(c_0_103,plain,(
    ! [X21] :
      ( ~ l1_struct_0(X21)
      | k2_struct_0(X21) = u1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),k2_struct_0(esk7_0))
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),esk8_0)
    | ~ l1_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_30])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),esk8_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ r3_lattices(esk7_0,X1,esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_23])])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_47]),c_0_98])]),c_0_48])).

cnf(c_0_107,negated_conjecture,
    ( r3_lattices(esk7_0,k4_lattices(esk7_0,esk5_1(esk8_0),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)),esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_77]),c_0_100])])).

cnf(c_0_108,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_109,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_47])).

cnf(c_0_110,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),k2_struct_0(esk7_0))
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_37]),c_0_38])])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107])])).

cnf(c_0_113,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),k2_struct_0(esk7_0),esk8_0),k2_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_116,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_117,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_113])).

cnf(c_0_118,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_30])).

cnf(c_0_120,negated_conjecture,
    ( ~ l1_struct_0(esk7_0)
    | ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_110])).

cnf(c_0_121,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(esk6_3(u1_struct_0(esk7_0),X1,esk8_0),esk8_0)
    | r2_hidden(esk6_3(u1_struct_0(esk7_0),X1,esk8_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_23])).

cnf(c_0_122,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_37]),c_0_38])])).

cnf(c_0_124,negated_conjecture,
    ( ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_30])).

cnf(c_0_125,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(u1_struct_0(esk7_0))) = esk8_0
    | r2_hidden(esk6_3(u1_struct_0(esk7_0),esk5_1(k1_zfmisc_1(u1_struct_0(esk7_0))),esk8_0),esk5_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    | r2_hidden(esk6_3(u1_struct_0(esk7_0),esk5_1(k1_zfmisc_1(u1_struct_0(esk7_0))),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_41])).

cnf(c_0_126,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_122]),c_0_118])])).

cnf(c_0_127,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_23])).

cnf(c_0_128,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( ~ r2_hidden(esk6_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_37]),c_0_38])])).

cnf(c_0_130,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_113]),c_0_126]),c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131])])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_132]),c_0_132]),c_0_126]),
    [proof]).

%------------------------------------------------------------------------------
