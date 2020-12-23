%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t50_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 224.31s
% Output     : CNFRefutation 224.31s
% Verified   : 
% Statistics : Number of formulae       :  105 (1114 expanded)
%              Number of clauses        :   67 ( 419 expanded)
%              Number of leaves         :   19 ( 278 expanded)
%              Depth                    :   27
%              Number of atoms          :  622 (7865 expanded)
%              Number of equality atoms :   63 ( 735 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',d21_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',dt_k15_lattice3)).

fof(t50_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1)
        & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',t50_lattice3)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',t7_boole)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',d17_lattice3)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',dt_o_0_0_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',existence_m1_subset_1)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',t26_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',t23_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',cc1_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',dt_k4_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',d16_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',dt_k5_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',redefinition_k4_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',commutativity_k4_lattices)).

fof(d13_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_lattices(X1,X2,X3) = X2
                  & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t50_lattice3.p',d13_lattices)).

fof(c_0_19,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r4_lattice3(X26,X28,X27)
        | X28 != k15_lattice3(X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | v2_struct_0(X26)
        | ~ l3_lattices(X26) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r4_lattice3(X26,X29,X27)
        | r1_lattices(X26,X28,X29)
        | X28 != k15_lattice3(X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | v2_struct_0(X26)
        | ~ l3_lattices(X26) )
      & ( m1_subset_1(esk6_3(X26,X27,X28),u1_struct_0(X26))
        | ~ r4_lattice3(X26,X28,X27)
        | X28 = k15_lattice3(X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | v2_struct_0(X26)
        | ~ l3_lattices(X26) )
      & ( r4_lattice3(X26,esk6_3(X26,X27,X28),X27)
        | ~ r4_lattice3(X26,X28,X27)
        | X28 = k15_lattice3(X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | v2_struct_0(X26)
        | ~ l3_lattices(X26) )
      & ( ~ r1_lattices(X26,X28,esk6_3(X26,X27,X28))
        | ~ r4_lattice3(X26,X28,X27)
        | X28 = k15_lattice3(X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | v2_struct_0(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_20,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ l3_lattices(X31)
      | m1_subset_1(k15_lattice3(X31,X32),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1)
          & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t50_lattice3])).

fof(c_0_23,plain,(
    ! [X85] :
      ( ~ v1_xboole_0(X85)
      | X85 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v4_lattice3(esk1_0)
    & l3_lattices(esk1_0)
    & ( v2_struct_0(esk1_0)
      | ~ v10_lattices(esk1_0)
      | ~ v13_lattices(esk1_0)
      | ~ l3_lattices(esk1_0)
      | k5_lattices(esk1_0) != k15_lattice3(esk1_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_27,plain,(
    ! [X86,X87] :
      ( ~ r2_hidden(X86,X87)
      | ~ v1_xboole_0(X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_28,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r4_lattice3(X20,X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X23,X22)
        | r1_lattices(X20,X23,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(esk5_3(X20,X21,X24),u1_struct_0(X20))
        | r4_lattice3(X20,X21,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( r2_hidden(esk5_3(X20,X21,X24),X24)
        | r4_lattice3(X20,X21,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( ~ r1_lattices(X20,esk5_3(X20,X21,X24),X21)
        | r4_lattice3(X20,X21,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_31,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk6_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk6_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,X1),X2)
    | ~ r4_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_42,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_39])).

fof(c_0_44,plain,(
    ! [X82,X83,X84] :
      ( ~ r2_hidden(X82,X83)
      | ~ m1_subset_1(X83,k1_zfmisc_1(X84))
      | ~ v1_xboole_0(X84) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_45,plain,(
    ! [X52] : m1_subset_1(esk11_1(X52),X52) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_46,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = k15_lattice3(esk1_0,X2)
    | ~ r4_lattice3(esk1_0,esk6_3(esk1_0,X2,k15_lattice3(esk1_0,X1)),X1)
    | ~ r4_lattice3(esk1_0,k15_lattice3(esk1_0,X1),X2)
    | ~ m1_subset_1(esk6_3(esk1_0,X2,k15_lattice3(esk1_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_47,plain,
    ( r4_lattice3(X1,X2,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk11_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k15_lattice3(esk1_0,k1_xboole_0) = k15_lattice3(esk1_0,X1)
    | ~ r4_lattice3(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1)
    | ~ m1_subset_1(esk6_3(esk1_0,X1,k15_lattice3(esk1_0,k1_xboole_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34])]),c_0_36])).

cnf(c_0_52,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk11_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k15_lattice3(esk1_0,k1_xboole_0) = k15_lattice3(esk1_0,X1)
    | ~ r4_lattice3(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_34]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_55,plain,
    ( r4_lattice3(X1,X2,esk11_1(k1_zfmisc_1(X3)))
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( k15_lattice3(esk1_0,esk11_1(k1_zfmisc_1(X1))) = k15_lattice3(esk1_0,k1_xboole_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_34])]),c_0_36])).

fof(c_0_57,plain,(
    ! [X72,X73,X74] :
      ( v2_struct_0(X72)
      | ~ v4_lattices(X72)
      | ~ l2_lattices(X72)
      | ~ m1_subset_1(X73,u1_struct_0(X72))
      | ~ m1_subset_1(X74,u1_struct_0(X72))
      | ~ r1_lattices(X72,X73,X74)
      | ~ r1_lattices(X72,X74,X73)
      | X73 = X74 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

fof(c_0_58,plain,(
    ! [X69,X70,X71] :
      ( v2_struct_0(X69)
      | ~ v6_lattices(X69)
      | ~ v8_lattices(X69)
      | ~ l3_lattices(X69)
      | ~ m1_subset_1(X70,u1_struct_0(X69))
      | ~ m1_subset_1(X71,u1_struct_0(X69))
      | r1_lattices(X69,k4_lattices(X69,X70,X71),X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

fof(c_0_59,plain,(
    ! [X46] :
      ( ( l1_lattices(X46)
        | ~ l3_lattices(X46) )
      & ( l2_lattices(X46)
        | ~ l3_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1)
    | ~ v1_xboole_0(X2)
    | ~ r4_lattice3(esk1_0,X1,esk11_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_34])]),c_0_36])).

cnf(c_0_65,plain,
    ( k4_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ r1_lattices(X1,X2,k4_lattices(X1,X2,X3))
    | ~ m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

fof(c_0_67,plain,(
    ! [X90] :
      ( ( ~ v2_struct_0(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) )
      & ( v4_lattices(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) )
      & ( v5_lattices(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) )
      & ( v6_lattices(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) )
      & ( v7_lattices(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) )
      & ( v8_lattices(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) )
      & ( v9_lattices(X90)
        | v2_struct_0(X90)
        | ~ v10_lattices(X90)
        | ~ l3_lattices(X90) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_68,negated_conjecture,
    ( k4_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1) = k15_lattice3(esk1_0,k1_xboole_0)
    | ~ v4_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_34])]),c_0_36])).

cnf(c_0_69,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_70,plain,(
    ! [X40,X41,X42] :
      ( v2_struct_0(X40)
      | ~ v6_lattices(X40)
      | ~ l1_lattices(X40)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | ~ m1_subset_1(X42,u1_struct_0(X40))
      | m1_subset_1(k4_lattices(X40,X41,X42),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

fof(c_0_71,plain,(
    ! [X16,X17,X18] :
      ( ( k2_lattices(X16,X17,X18) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | X17 != k5_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,X18,X17) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | X17 != k5_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( m1_subset_1(esk4_2(X16,X17),u1_struct_0(X16))
        | X17 = k5_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,X17,esk4_2(X16,X17)) != X17
        | k2_lattices(X16,esk4_2(X16,X17),X17) != X17
        | X17 = k5_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_72,plain,(
    ! [X43] :
      ( v2_struct_0(X43)
      | ~ l1_lattices(X43)
      | m1_subset_1(k5_lattices(X43),u1_struct_0(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_73,plain,(
    ! [X58,X59,X60] :
      ( v2_struct_0(X58)
      | ~ v6_lattices(X58)
      | ~ l1_lattices(X58)
      | ~ m1_subset_1(X59,u1_struct_0(X58))
      | ~ m1_subset_1(X60,u1_struct_0(X58))
      | k4_lattices(X58,X59,X60) = k2_lattices(X58,X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_74,negated_conjecture,
    ( k4_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1) = k15_lattice3(esk1_0,k1_xboole_0)
    | ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k4_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1) = k15_lattice3(esk1_0,k1_xboole_0)
    | ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ v10_lattices(esk1_0)
    | ~ v13_lattices(esk1_0)
    | ~ l3_lattices(esk1_0)
    | k5_lattices(esk1_0) != k15_lattice3(esk1_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_81,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k2_lattices(esk1_0,k15_lattice3(esk1_0,k1_xboole_0),X1) = k15_lattice3(esk1_0,k1_xboole_0)
    | ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_36])).

cnf(c_0_83,negated_conjecture,
    ( k15_lattice3(esk1_0,k1_xboole_0) != k5_lattices(esk1_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_35]),c_0_34])]),c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ v13_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_36]),c_0_83])).

fof(c_0_85,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v6_lattices(X8)
      | ~ l1_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k4_lattices(X8,X9,X10) = k4_lattices(X8,X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_25]),c_0_34])]),c_0_36])).

cnf(c_0_87,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_90,plain,(
    ! [X11,X13,X14] :
      ( ( m1_subset_1(esk2_1(X11),u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,esk2_1(X11),X13) = esk2_1(X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,X13,esk2_1(X11)) = esk2_1(X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( m1_subset_1(esk3_2(X11,X14),u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,X14,esk3_2(X11,X14)) != X14
        | k2_lattices(X11,esk3_2(X11,X14),X14) != X14
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_91,plain,
    ( k4_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_77]),c_0_36])).

cnf(c_0_93,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_94,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( k2_lattices(esk1_0,X1,k15_lattice3(esk1_0,k1_xboole_0)) = k15_lattice3(esk1_0,k1_xboole_0)
    | ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_79]),c_0_36])).

cnf(c_0_96,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_97,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(esk3_2(esk1_0,k15_lattice3(esk1_0,k1_xboole_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_36]),c_0_82]),c_0_96])).

cnf(c_0_98,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ m1_subset_1(k15_lattice3(esk1_0,k1_xboole_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_36]),c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_25]),c_0_34])]),c_0_36])).

cnf(c_0_101,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_87]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_102,negated_conjecture,
    ( ~ l1_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_93]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_103,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
