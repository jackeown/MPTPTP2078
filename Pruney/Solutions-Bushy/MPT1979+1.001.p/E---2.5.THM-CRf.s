%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 563 expanded)
%              Number of clauses        :   66 ( 177 expanded)
%              Number of leaves         :   13 ( 141 expanded)
%              Depth                    :   17
%              Number of atoms          :  768 (8273 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :  119 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( ~ r2_hidden(X3,X2)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v1_waybel_7(X4,X1)
                          & r1_tarski(X2,X4)
                          & ~ r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_waybel_7)).

fof(t27_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & v2_waybel_0(X3,X1)
                & v13_waybel_0(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ~ ( r1_subset_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v1_waybel_7(X4,X1)
                          & r1_tarski(X2,X4)
                          & r1_subset_1(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_7)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k6_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(d19_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X4,X3) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_waybel_0)).

fof(t18_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k6_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(fc9_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k6_waybel_0(X1,X2))
        & v2_waybel_0(k6_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_waybel_0)).

fof(fc13_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v13_waybel_0(k6_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_waybel_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_waybel_1(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( ~ r2_hidden(X3,X2)
                    & ! [X4] :
                        ( ( ~ v1_xboole_0(X4)
                          & v1_waybel_0(X4,X1)
                          & v12_waybel_0(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( v1_waybel_7(X4,X1)
                            & r1_tarski(X2,X4)
                            & ~ r2_hidden(X3,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_waybel_7])).

fof(c_0_14,negated_conjecture,(
    ! [X45] :
      ( v3_orders_2(esk5_0)
      & v4_orders_2(esk5_0)
      & v5_orders_2(esk5_0)
      & v2_waybel_1(esk5_0)
      & v1_lattice3(esk5_0)
      & v2_lattice3(esk5_0)
      & l1_orders_2(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & v1_waybel_0(esk6_0,esk5_0)
      & v12_waybel_0(esk6_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
      & ~ r2_hidden(esk7_0,esk6_0)
      & ( v1_xboole_0(X45)
        | ~ v1_waybel_0(X45,esk5_0)
        | ~ v12_waybel_0(X45,esk5_0)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v1_waybel_7(X45,esk5_0)
        | ~ r1_tarski(esk6_0,X45)
        | r2_hidden(esk7_0,X45) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

fof(c_0_15,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v1_xboole_0(esk3_3(X29,X30,X31))
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( v1_waybel_0(esk3_3(X29,X30,X31),X29)
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( v12_waybel_0(esk3_3(X29,X30,X31),X29)
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( m1_subset_1(esk3_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( v1_waybel_7(esk3_3(X29,X30,X31),X29)
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( r1_tarski(X30,esk3_3(X29,X30,X31))
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( r1_subset_1(esk3_3(X29,X30,X31),X31)
        | ~ r1_subset_1(X30,X31)
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,X29)
        | ~ v13_waybel_0(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,X29)
        | ~ v12_waybel_0(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_waybel_1(X29)
        | ~ v1_lattice3(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_waybel_7])])])])])])).

fof(c_0_16,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | m1_subset_1(X39,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | m1_subset_1(k6_waybel_0(X12,X13),k1_zfmisc_1(u1_struct_0(X12))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_waybel_0])])])).

fof(c_0_18,plain,(
    ! [X33,X34,X36,X37,X38] :
      ( ( r2_hidden(esk4_2(X33,X34),X33)
        | r1_xboole_0(X33,X34) )
      & ( r2_hidden(esk4_2(X33,X34),X34)
        | r1_xboole_0(X33,X34) )
      & ( ~ r2_hidden(X38,X36)
        | ~ r2_hidden(X38,X37)
        | ~ r1_xboole_0(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ( ~ r1_subset_1(X18,X19)
        | r1_xboole_0(X18,X19)
        | v1_xboole_0(X18)
        | v1_xboole_0(X19) )
      & ( ~ r1_xboole_0(X18,X19)
        | r1_subset_1(X18,X19)
        | v1_xboole_0(X18)
        | v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_0,X1)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_waybel_7(X1,esk5_0)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,esk3_3(X2,X1,X3))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,X3)
    | ~ v2_waybel_0(X3,X2)
    | ~ v13_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(esk3_3(X1,esk6_0,X2))
    | v1_xboole_0(X2)
    | r2_hidden(esk7_0,esk3_3(X1,esk6_0,X2))
    | ~ v1_waybel_7(esk3_3(X1,esk6_0,X2),esk5_0)
    | ~ v1_waybel_0(esk3_3(X1,esk6_0,X2),esk5_0)
    | ~ v1_waybel_0(esk6_0,X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_subset_1(esk6_0,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v3_orders_2(X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ v4_orders_2(X1)
    | ~ v12_waybel_0(esk3_3(X1,esk6_0,X2),esk5_0)
    | ~ v12_waybel_0(esk6_0,X1)
    | ~ m1_subset_1(esk3_3(X1,esk6_0,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( v1_waybel_7(esk3_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( v2_waybel_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v12_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_39,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(X8,X7)
        | ~ r1_orders_2(X6,X9,X8)
        | r2_hidden(X9,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),u1_struct_0(X6))
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk2_2(X6,X7),esk1_2(X6,X7))
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),X7)
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_waybel_0])])])])])).

fof(c_0_40,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r2_hidden(X28,k6_waybel_0(X26,X27))
        | r1_orders_2(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ r1_orders_2(X26,X27,X28)
        | r2_hidden(X28,k6_waybel_0(X26,X27))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_waybel_0])])])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k6_waybel_0(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_42,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_44,plain,
    ( r1_subset_1(esk3_3(X1,X2,X3),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(esk3_3(X1,X2,X3))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,esk6_0,X1))
    | v1_xboole_0(X1)
    | r2_hidden(esk7_0,esk3_3(esk5_0,esk6_0,X1))
    | ~ v1_waybel_0(esk3_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r1_subset_1(esk6_0,X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(esk3_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_22])).

cnf(c_0_47,plain,
    ( v1_waybel_0(esk3_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( r1_orders_2(X2,X3,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k6_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k6_waybel_0(X1,X2),X3)
    | m1_subset_1(esk4_2(k6_waybel_0(X1,X2),X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X1,X3)
    | ~ v1_lattice3(X3)
    | ~ v2_waybel_1(X3)
    | ~ v5_orders_2(X3)
    | ~ r1_subset_1(X1,X2)
    | ~ v2_waybel_0(X2,X3)
    | ~ v3_orders_2(X3)
    | ~ v13_waybel_0(X2,X3)
    | ~ v4_orders_2(X3)
    | ~ r2_hidden(X4,esk3_3(X3,X1,X2))
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_lattice3(X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,esk6_0,X1))
    | v1_xboole_0(X1)
    | r2_hidden(esk7_0,esk3_3(esk5_0,esk6_0,X1))
    | ~ r1_subset_1(esk6_0,X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(esk3_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_22])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_48,c_0_23])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k6_waybel_0(X1,X2),X3)
    | r1_orders_2(X1,X2,esk4_2(k6_waybel_0(X1,X2),X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,esk6_0,X1))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(esk6_0,X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ v12_waybel_0(esk3_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_22])).

cnf(c_0_56,plain,
    ( v12_waybel_0(esk3_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k6_waybel_0(X1,X2),X3)
    | r2_hidden(X2,X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk4_2(k6_waybel_0(X1,X2),X3),X4)
    | ~ v12_waybel_0(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,esk6_0,X1))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(esk6_0,X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_22])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_61,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k6_waybel_0(X1,X2),X3)
    | r2_hidden(X2,X3)
    | v2_struct_0(X1)
    | ~ v12_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,esk6_0,X1))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(esk6_0,X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_22])).

fof(c_0_64,plain,(
    ! [X16,X17] :
      ( ( ~ v1_xboole_0(k6_waybel_0(X16,X17))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16)) )
      & ( v2_waybel_0(k6_waybel_0(X16,X17),X16)
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_waybel_0])])])])).

cnf(c_0_65,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X4,k6_waybel_0(X3,X1))
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r1_subset_1(esk6_0,X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_63]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_22])).

cnf(c_0_68,plain,
    ( v2_waybel_0(k6_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_37]),c_0_38])])).

fof(c_0_70,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v4_orders_2(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | v13_waybel_0(k6_waybel_0(X14,X15),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc13_waybel_0])])])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k6_waybel_0(X2,X3))
    | r2_hidden(X3,X4)
    | v2_struct_0(X2)
    | ~ r2_hidden(esk4_2(X1,k6_waybel_0(X2,X3)),X4)
    | ~ v12_waybel_0(X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk5_0,X1))
    | ~ r1_subset_1(esk6_0,k6_waybel_0(esk5_0,X1))
    | ~ v13_waybel_0(k6_waybel_0(esk5_0,X1),esk5_0)
    | ~ r2_hidden(esk7_0,k6_waybel_0(esk5_0,X1))
    | ~ m1_subset_1(k6_waybel_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_33]),c_0_38])]),c_0_69])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | v13_waybel_0(k6_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( r1_subset_1(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,k6_waybel_0(X2,X3))
    | r2_hidden(X3,X1)
    | v2_struct_0(X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk5_0,X1))
    | ~ r1_subset_1(esk6_0,k6_waybel_0(esk5_0,X1))
    | ~ r2_hidden(esk7_0,k6_waybel_0(esk5_0,X1))
    | ~ m1_subset_1(k6_waybel_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_34]),c_0_38])]),c_0_69])).

cnf(c_0_77,plain,
    ( r1_subset_1(X1,k6_waybel_0(X2,X3))
    | v1_xboole_0(k6_waybel_0(X2,X3))
    | v1_xboole_0(X1)
    | r2_hidden(X3,X1)
    | v2_struct_0(X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk5_0,X1))
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(esk7_0,k6_waybel_0(esk5_0,X1))
    | ~ m1_subset_1(k6_waybel_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_35]),c_0_36]),c_0_38])]),c_0_22]),c_0_69])).

cnf(c_0_79,plain,
    ( r2_hidden(X3,k6_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_81,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v3_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | r3_orders_2(X23,X24,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk5_0,X1))
    | r2_hidden(X1,esk6_0)
    | ~ r1_orders_2(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(k6_waybel_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_38])]),c_0_69])).

fof(c_0_83,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r3_orders_2(X20,X21,X22)
        | r1_orders_2(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) )
      & ( ~ r1_orders_2(X20,X21,X22)
        | r3_orders_2(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k6_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk5_0,X1))
    | r2_hidden(X1,esk6_0)
    | ~ r1_orders_2(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_24]),c_0_38])]),c_0_69])).

cnf(c_0_87,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r3_orders_2(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_80]),c_0_33]),c_0_38])]),c_0_69])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r1_orders_2(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_33]),c_0_38])]),c_0_69])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_33]),c_0_38])]),c_0_69])).

cnf(c_0_91,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_80])]),c_0_91]),
    [proof]).

%------------------------------------------------------------------------------
