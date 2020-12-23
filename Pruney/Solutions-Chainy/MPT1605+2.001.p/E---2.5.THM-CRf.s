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
% DateTime   : Thu Dec  3 11:15:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 344 expanded)
%              Number of clauses        :   56 ( 143 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  387 ( 972 expanded)
%              Number of equality atoms :   23 ( 153 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

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

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(d4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r1_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ r1_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_hidden(X28,X26)
        | r1_orders_2(X25,X27,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))
        | r1_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X26)
        | r1_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ r1_orders_2(X25,X27,esk3_3(X25,X26,X27))
        | r1_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_23,plain,(
    ! [X50] :
      ( u1_struct_0(k2_yellow_1(X50)) = X50
      & u1_orders_2(k2_yellow_1(X50)) = k1_yellow_1(X50) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_24,plain,(
    ! [X48] :
      ( v1_orders_2(k2_yellow_1(X48))
      & l1_orders_2(k2_yellow_1(X48)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    & r2_hidden(k1_xboole_0,esk7_0)
    & k3_yellow_0(k2_yellow_1(esk7_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_27,plain,(
    ! [X51,X52,X53] :
      ( ( ~ r3_orders_2(k2_yellow_1(X51),X52,X53)
        | r1_tarski(X52,X53)
        | ~ m1_subset_1(X53,u1_struct_0(k2_yellow_1(X51)))
        | ~ m1_subset_1(X52,u1_struct_0(k2_yellow_1(X51)))
        | v1_xboole_0(X51) )
      & ( ~ r1_tarski(X52,X53)
        | r3_orders_2(k2_yellow_1(X51),X52,X53)
        | ~ m1_subset_1(X53,u1_struct_0(k2_yellow_1(X51)))
        | ~ m1_subset_1(X52,u1_struct_0(k2_yellow_1(X51)))
        | v1_xboole_0(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_28,plain,(
    ! [X46] :
      ( ~ l1_orders_2(X46)
      | m1_subset_1(k3_yellow_0(X46),u1_struct_0(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_37,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,plain,
    ( r1_lattice3(k2_yellow_1(X1),X2,X3)
    | m1_subset_1(esk3_3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_30]),c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_31])])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | m1_subset_1(esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_46,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r3_orders_2(X19,X20,X21)
        | r1_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) )
      & ( ~ r1_orders_2(X19,X20,X21)
        | r3_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_47,plain,(
    ! [X49] :
      ( v1_orders_2(k2_yellow_1(X49))
      & v3_orders_2(k2_yellow_1(X49))
      & v4_orders_2(k2_yellow_1(X49))
      & v5_orders_2(k2_yellow_1(X49)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

cnf(c_0_48,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,k3_yellow_0(k2_yellow_1(X1)))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,k3_yellow_0(k2_yellow_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | r3_orders_2(k2_yellow_1(esk7_0),X2,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))
    | ~ m1_subset_1(X2,esk7_0)
    | ~ r1_tarski(X2,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_44]),c_0_45])).

fof(c_0_51,plain,(
    ! [X22,X23,X24] :
      ( ~ v5_orders_2(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | ~ r1_orders_2(X22,X23,X24)
      | ~ r1_orders_2(X22,X24,X23)
      | X23 = X24 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_52,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,k3_yellow_0(k2_yellow_1(X1)))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | r3_orders_2(k2_yellow_1(esk7_0),X2,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))
    | ~ m1_subset_1(X2,esk7_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_57,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_53]),c_0_31])])).

cnf(c_0_60,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_55])]),c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | r3_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_39]),c_0_55])])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_orders_2(k2_yellow_1(X3),X2,X1)
    | ~ r1_orders_2(k2_yellow_1(X3),X1,X2)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_58]),c_0_31])])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk7_0)))
    | v2_struct_0(k2_yellow_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_41]),c_0_39])])).

cnf(c_0_64,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk7_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_65,plain,(
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | k3_yellow_0(X35) = k1_yellow_0(X35,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_66,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_lattice3(X39,X40,X41)
        | X41 != k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r2_lattice3(X39,X40,X42)
        | r1_orders_2(X39,X41,X42)
        | X41 != k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( m1_subset_1(esk6_3(X39,X40,X41),u1_struct_0(X39))
        | ~ r2_lattice3(X39,X40,X41)
        | X41 = k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( r2_lattice3(X39,X40,esk6_3(X39,X40,X41))
        | ~ r2_lattice3(X39,X40,X41)
        | X41 = k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( ~ r1_orders_2(X39,X41,esk6_3(X39,X40,X41))
        | ~ r2_lattice3(X39,X40,X41)
        | X41 = k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_67,plain,(
    ! [X44,X45] :
      ( ~ l1_orders_2(X44)
      | m1_subset_1(k1_yellow_0(X44,X45),u1_struct_0(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_68,plain,(
    ! [X36,X38] :
      ( ( m1_subset_1(esk5_1(X36),u1_struct_0(X36))
        | ~ v1_yellow_0(X36)
        | ~ l1_orders_2(X36) )
      & ( r1_lattice3(X36,u1_struct_0(X36),esk5_1(X36))
        | ~ v1_yellow_0(X36)
        | ~ l1_orders_2(X36) )
      & ( ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ r1_lattice3(X36,u1_struct_0(X36),X38)
        | v1_yellow_0(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).

cnf(c_0_69,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk3_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | r1_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_61]),c_0_39])]),c_0_44])).

fof(c_0_71,plain,(
    ! [X17] :
      ( ~ v2_struct_0(X17)
      | ~ l1_struct_0(X17)
      | v1_xboole_0(u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_72,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk7_0))
    | ~ r1_orders_2(k2_yellow_1(esk7_0),k3_yellow_0(k2_yellow_1(esk7_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_39]),c_0_41])]),c_0_64])).

cnf(c_0_74,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_77,plain,(
    ! [X47] :
      ( ( r1_yellow_0(X47,k1_xboole_0)
        | v2_struct_0(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ l1_orders_2(X47) )
      & ( r2_yellow_0(X47,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ l1_orders_2(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_78,plain,
    ( v1_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | v2_struct_0(k2_yellow_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31]),c_0_30]),c_0_39])])).

fof(c_0_80,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X33,X31)
        | r1_orders_2(X30,X33,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk4_3(X30,X31,X32),u1_struct_0(X30))
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(esk4_3(X30,X31,X32),X31)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ r1_orders_2(X30,esk4_3(X30,X31,X32),X32)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_81,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk7_0))
    | ~ r1_orders_2(k2_yellow_1(esk7_0),k1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_31])])).

cnf(c_0_84,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_75]),c_0_76])).

cnf(c_0_85,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( v1_yellow_0(k2_yellow_1(esk7_0))
    | v2_struct_0(k2_yellow_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_31]),c_0_30]),c_0_39])])).

cnf(c_0_87,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk7_0))
    | ~ r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)
    | ~ r2_lattice3(k2_yellow_1(esk7_0),k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_31]),c_0_30]),c_0_39])])).

cnf(c_0_90,negated_conjecture,
    ( r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_58]),c_0_31])])).

cnf(c_0_91,plain,
    ( r2_lattice3(k2_yellow_1(X1),X2,X3)
    | r2_hidden(esk4_3(k2_yellow_1(X1),X2,X3),X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_30]),c_0_31])])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)
    | ~ r2_lattice3(k2_yellow_1(esk7_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_30]),c_0_31])]),c_0_45])).

cnf(c_0_93,negated_conjecture,
    ( r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_90]),c_0_30]),c_0_31])]),c_0_45])).

cnf(c_0_94,negated_conjecture,
    ( r2_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | r2_hidden(esk4_3(k2_yellow_1(esk7_0),X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_lattice3(k2_yellow_1(esk7_0),k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_96,negated_conjecture,
    ( r2_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.031 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.20/0.47  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.20/0.47  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.47  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.47  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.47  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.47  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.20/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.47  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.47  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.47  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 0.20/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.47  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.20/0.47  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.20/0.47  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.20/0.47  fof(d4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v1_yellow_0(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&r1_lattice3(X1,u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_yellow_0)).
% 0.20/0.47  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.20/0.47  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.47  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.20/0.47  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.20/0.47  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.20/0.47  fof(c_0_22, plain, ![X25, X26, X27, X28]:((~r1_lattice3(X25,X26,X27)|(~m1_subset_1(X28,u1_struct_0(X25))|(~r2_hidden(X28,X26)|r1_orders_2(X25,X27,X28)))|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&((m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))|r1_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&((r2_hidden(esk3_3(X25,X26,X27),X26)|r1_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&(~r1_orders_2(X25,X27,esk3_3(X25,X26,X27))|r1_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.20/0.47  fof(c_0_23, plain, ![X50]:(u1_struct_0(k2_yellow_1(X50))=X50&u1_orders_2(k2_yellow_1(X50))=k1_yellow_1(X50)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.47  fof(c_0_24, plain, ![X48]:(v1_orders_2(k2_yellow_1(X48))&l1_orders_2(k2_yellow_1(X48))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.47  fof(c_0_25, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.47  fof(c_0_26, negated_conjecture, (~v1_xboole_0(esk7_0)&(r2_hidden(k1_xboole_0,esk7_0)&k3_yellow_0(k2_yellow_1(esk7_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.20/0.47  fof(c_0_27, plain, ![X51, X52, X53]:((~r3_orders_2(k2_yellow_1(X51),X52,X53)|r1_tarski(X52,X53)|~m1_subset_1(X53,u1_struct_0(k2_yellow_1(X51)))|~m1_subset_1(X52,u1_struct_0(k2_yellow_1(X51)))|v1_xboole_0(X51))&(~r1_tarski(X52,X53)|r3_orders_2(k2_yellow_1(X51),X52,X53)|~m1_subset_1(X53,u1_struct_0(k2_yellow_1(X51)))|~m1_subset_1(X52,u1_struct_0(k2_yellow_1(X51)))|v1_xboole_0(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.47  fof(c_0_28, plain, ![X46]:(~l1_orders_2(X46)|m1_subset_1(k3_yellow_0(X46),u1_struct_0(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.20/0.47  cnf(c_0_29, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_30, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_31, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.47  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (r2_hidden(k1_xboole_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_34, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_35, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.47  fof(c_0_36, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.47  fof(c_0_37, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.47  cnf(c_0_38, plain, (r1_lattice3(k2_yellow_1(X1),X2,X3)|m1_subset_1(esk3_3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.47  cnf(c_0_39, negated_conjecture, (m1_subset_1(k1_xboole_0,esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.47  cnf(c_0_40, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_30]), c_0_30])).
% 0.20/0.47  cnf(c_0_41, plain, (m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_31])])).
% 0.20/0.47  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_43, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.47  cnf(c_0_44, negated_conjecture, (r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|m1_subset_1(esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0),esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  fof(c_0_46, plain, ![X19, X20, X21]:((~r3_orders_2(X19,X20,X21)|r1_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))&(~r1_orders_2(X19,X20,X21)|r3_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.47  fof(c_0_47, plain, ![X49]:(((v1_orders_2(k2_yellow_1(X49))&v3_orders_2(k2_yellow_1(X49)))&v4_orders_2(k2_yellow_1(X49)))&v5_orders_2(k2_yellow_1(X49))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.47  cnf(c_0_48, plain, (r3_orders_2(k2_yellow_1(X1),X2,k3_yellow_0(k2_yellow_1(X1)))|v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,k3_yellow_0(k2_yellow_1(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.47  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.47  cnf(c_0_50, negated_conjecture, (r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|r3_orders_2(k2_yellow_1(esk7_0),X2,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))|~m1_subset_1(X2,esk7_0)|~r1_tarski(X2,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_44]), c_0_45])).
% 0.20/0.47  fof(c_0_51, plain, ![X22, X23, X24]:(~v5_orders_2(X22)|~l1_orders_2(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~m1_subset_1(X24,u1_struct_0(X22))|(~r1_orders_2(X22,X23,X24)|~r1_orders_2(X22,X24,X23)|X23=X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.20/0.47  cnf(c_0_52, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.47  cnf(c_0_53, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.47  cnf(c_0_54, plain, (r3_orders_2(k2_yellow_1(X1),X2,k3_yellow_0(k2_yellow_1(X1)))|v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.47  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|r3_orders_2(k2_yellow_1(esk7_0),X2,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))|~m1_subset_1(X2,esk7_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.20/0.47  cnf(c_0_57, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.47  cnf(c_0_58, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.47  cnf(c_0_59, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_30]), c_0_53]), c_0_31])])).
% 0.20/0.47  cnf(c_0_60, negated_conjecture, (r3_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_39]), c_0_55])]), c_0_45])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|r3_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_39]), c_0_55])])).
% 0.20/0.47  cnf(c_0_62, plain, (X1=X2|~r1_orders_2(k2_yellow_1(X3),X2,X1)|~r1_orders_2(k2_yellow_1(X3),X1,X2)|~m1_subset_1(X2,X3)|~m1_subset_1(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_58]), c_0_31])])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, (r1_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk7_0)))|v2_struct_0(k2_yellow_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_41]), c_0_39])])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk7_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  fof(c_0_65, plain, ![X35]:(~l1_orders_2(X35)|k3_yellow_0(X35)=k1_yellow_0(X35,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.20/0.47  fof(c_0_66, plain, ![X39, X40, X41, X42]:(((r2_lattice3(X39,X40,X41)|X41!=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r2_lattice3(X39,X40,X42)|r1_orders_2(X39,X41,X42))|X41!=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39)))&((m1_subset_1(esk6_3(X39,X40,X41),u1_struct_0(X39))|~r2_lattice3(X39,X40,X41)|X41=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))&((r2_lattice3(X39,X40,esk6_3(X39,X40,X41))|~r2_lattice3(X39,X40,X41)|X41=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))&(~r1_orders_2(X39,X41,esk6_3(X39,X40,X41))|~r2_lattice3(X39,X40,X41)|X41=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.20/0.47  fof(c_0_67, plain, ![X44, X45]:(~l1_orders_2(X44)|m1_subset_1(k1_yellow_0(X44,X45),u1_struct_0(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.20/0.47  fof(c_0_68, plain, ![X36, X38]:(((m1_subset_1(esk5_1(X36),u1_struct_0(X36))|~v1_yellow_0(X36)|~l1_orders_2(X36))&(r1_lattice3(X36,u1_struct_0(X36),esk5_1(X36))|~v1_yellow_0(X36)|~l1_orders_2(X36)))&(~m1_subset_1(X38,u1_struct_0(X36))|~r1_lattice3(X36,u1_struct_0(X36),X38)|v1_yellow_0(X36)|~l1_orders_2(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).
% 0.20/0.47  cnf(c_0_69, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk3_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|r1_orders_2(k2_yellow_1(esk7_0),k1_xboole_0,esk3_3(k2_yellow_1(esk7_0),X1,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_61]), c_0_39])]), c_0_44])).
% 0.20/0.47  fof(c_0_71, plain, ![X17]:(~v2_struct_0(X17)|~l1_struct_0(X17)|v1_xboole_0(u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.20/0.47  fof(c_0_72, plain, ![X18]:(~l1_orders_2(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (v2_struct_0(k2_yellow_1(esk7_0))|~r1_orders_2(k2_yellow_1(esk7_0),k3_yellow_0(k2_yellow_1(esk7_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_39]), c_0_41])]), c_0_64])).
% 0.20/0.47  cnf(c_0_74, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.47  cnf(c_0_75, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.47  cnf(c_0_76, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.47  fof(c_0_77, plain, ![X47]:((r1_yellow_0(X47,k1_xboole_0)|(v2_struct_0(X47)|~v5_orders_2(X47)|~v1_yellow_0(X47)|~l1_orders_2(X47)))&(r2_yellow_0(X47,u1_struct_0(X47))|(v2_struct_0(X47)|~v5_orders_2(X47)|~v1_yellow_0(X47)|~l1_orders_2(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.20/0.47  cnf(c_0_78, plain, (v1_yellow_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,u1_struct_0(X2),X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (r1_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|v2_struct_0(k2_yellow_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_31]), c_0_30]), c_0_39])])).
% 0.20/0.47  fof(c_0_80, plain, ![X30, X31, X32, X33]:((~r2_lattice3(X30,X31,X32)|(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X33,X31)|r1_orders_2(X30,X33,X32)))|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((m1_subset_1(esk4_3(X30,X31,X32),u1_struct_0(X30))|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((r2_hidden(esk4_3(X30,X31,X32),X31)|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&(~r1_orders_2(X30,esk4_3(X30,X31,X32),X32)|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.20/0.47  cnf(c_0_81, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.47  cnf(c_0_82, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.47  cnf(c_0_83, negated_conjecture, (v2_struct_0(k2_yellow_1(esk7_0))|~r1_orders_2(k2_yellow_1(esk7_0),k1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_31])])).
% 0.20/0.47  cnf(c_0_84, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_75]), c_0_76])).
% 0.20/0.47  cnf(c_0_85, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (v1_yellow_0(k2_yellow_1(esk7_0))|v2_struct_0(k2_yellow_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_31]), c_0_30]), c_0_39])])).
% 0.20/0.47  cnf(c_0_87, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.47  cnf(c_0_88, plain, (v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)|~v2_struct_0(X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.47  cnf(c_0_89, negated_conjecture, (v2_struct_0(k2_yellow_1(esk7_0))|~r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)|~r2_lattice3(k2_yellow_1(esk7_0),k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_31]), c_0_30]), c_0_39])])).
% 0.20/0.47  cnf(c_0_90, negated_conjecture, (r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)|v2_struct_0(k2_yellow_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_58]), c_0_31])])).
% 0.20/0.47  cnf(c_0_91, plain, (r2_lattice3(k2_yellow_1(X1),X2,X3)|r2_hidden(esk4_3(k2_yellow_1(X1),X2,X3),X2)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_30]), c_0_31])])).
% 0.20/0.47  cnf(c_0_92, negated_conjecture, (~r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)|~r2_lattice3(k2_yellow_1(esk7_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_30]), c_0_31])]), c_0_45])).
% 0.20/0.47  cnf(c_0_93, negated_conjecture, (r1_yellow_0(k2_yellow_1(esk7_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_90]), c_0_30]), c_0_31])]), c_0_45])).
% 0.20/0.47  cnf(c_0_94, negated_conjecture, (r2_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|r2_hidden(esk4_3(k2_yellow_1(esk7_0),X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_91, c_0_39])).
% 0.20/0.47  cnf(c_0_95, negated_conjecture, (~r2_lattice3(k2_yellow_1(esk7_0),k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 0.20/0.47  cnf(c_0_96, negated_conjecture, (r2_lattice3(k2_yellow_1(esk7_0),X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_94])).
% 0.20/0.47  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_55])]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 98
% 0.20/0.47  # Proof object clause steps            : 56
% 0.20/0.47  # Proof object formula steps           : 42
% 0.20/0.47  # Proof object conjectures             : 26
% 0.20/0.47  # Proof object clause conjectures      : 23
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 25
% 0.20/0.47  # Proof object initial formulas used   : 21
% 0.20/0.47  # Proof object generating inferences   : 28
% 0.20/0.47  # Proof object simplifying inferences  : 61
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 21
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 46
% 0.20/0.47  # Removed in clause preprocessing      : 1
% 0.20/0.47  # Initial clauses in saturation        : 45
% 0.20/0.47  # Processed clauses                    : 661
% 0.20/0.47  # ...of these trivial                  : 1
% 0.20/0.47  # ...subsumed                          : 153
% 0.20/0.47  # ...remaining for further processing  : 507
% 0.20/0.47  # Other redundant clauses eliminated   : 2
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 31
% 0.20/0.47  # Backward-rewritten                   : 4
% 0.20/0.47  # Generated clauses                    : 1699
% 0.20/0.47  # ...of the previous two non-trivial   : 1637
% 0.20/0.47  # Contextual simplify-reflections      : 32
% 0.20/0.47  # Paramodulations                      : 1679
% 0.20/0.47  # Factorizations                       : 2
% 0.20/0.47  # Equation resolutions                 : 2
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 410
% 0.20/0.47  #    Positive orientable unit clauses  : 19
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 4
% 0.20/0.47  #    Non-unit-clauses                  : 387
% 0.20/0.47  # Current number of unprocessed clauses: 1045
% 0.20/0.47  # ...number of literals in the above   : 4913
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 96
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 36027
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 15212
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 211
% 0.20/0.47  # Unit Clause-clause subsumption calls : 265
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 11
% 0.20/0.47  # BW rewrite match successes           : 3
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 57272
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.125 s
% 0.20/0.48  # System time              : 0.008 s
% 0.20/0.48  # Total time               : 0.133 s
% 0.20/0.48  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
