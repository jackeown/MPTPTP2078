%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1981+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:06 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  207 (8861 expanded)
%              Number of clauses        :  164 (3690 expanded)
%              Number of leaves         :   21 (2190 expanded)
%              Depth                    :   30
%              Number of atoms          : 1166 (71266 expanded)
%              Number of equality atoms :   30 (4090 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :  119 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t30_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v11_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(X1))
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v1_xboole_0(X3)
              & v2_waybel_0(X3,X1)
              & v13_waybel_0(X3,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
              & r1_tarski(X2,X3)
              & v3_waybel_7(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_7)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t29_waybel_7,axiom,(
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
                        & v2_waybel_0(X4,X1)
                        & v13_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v2_waybel_7(X4,X1)
                          & r1_tarski(X3,X4)
                          & r1_subset_1(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(t23_waybel_4,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => k5_waybel_0(X1,k3_yellow_0(X1)) = k6_domain_1(u1_struct_0(X1),k3_yellow_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_4)).

fof(cc8_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_yellow_0(X1)
          & v2_waybel_1(X1)
          & v10_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(cc4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_yellow_0(X1)
       => ( v1_yellow_0(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(t8_waybel_7,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(symmetry_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
       => r1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(t26_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v11_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( ( v1_subset_1(X2,u1_struct_0(X1))
              & v2_waybel_7(X2,X1) )
          <=> v3_waybel_7(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_7)).

fof(c_0_21,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_23,plain,(
    ! [X41,X42,X44,X45,X46] :
      ( ( r2_hidden(esk4_2(X41,X42),X41)
        | r1_xboole_0(X41,X42) )
      & ( r2_hidden(esk4_2(X41,X42),X42)
        | r1_xboole_0(X41,X42) )
      & ( ~ r2_hidden(X46,X44)
        | ~ r2_hidden(X46,X45)
        | ~ r1_xboole_0(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( esk4_2(X1,k1_tarski(X2)) = X2
    | r1_xboole_0(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_tarski(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(esk4_2(X1,k1_tarski(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_32,plain,
    ( esk4_2(k1_tarski(X1),X2) = X1
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

fof(c_0_33,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X39,X40)
      | v1_xboole_0(X40)
      | r2_hidden(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_34,plain,(
    ! [X18] : m1_subset_1(esk2_1(X18),X18) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_35,plain,(
    ! [X50,X51] :
      ( ~ r2_hidden(X50,X51)
      | ~ v1_xboole_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_tarski(esk4_2(X1,X2)),k1_tarski(X3))
    | r1_xboole_0(X1,X2)
    | r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k1_tarski(esk4_2(X1,X2)))
    | ~ r2_hidden(X4,k1_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_46,plain,
    ( esk2_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_43]),c_0_44])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v7_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v11_waybel_1(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(X1))
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ? [X3] :
                ( ~ v1_xboole_0(X3)
                & v2_waybel_0(X3,X1)
                & v13_waybel_0(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                & r1_tarski(X2,X3)
                & v3_waybel_7(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_waybel_7])).

fof(c_0_48,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | k6_domain_1(X24,X25) = k1_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_49,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | m1_subset_1(k3_yellow_0(X15),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k1_tarski(esk4_2(X1,X2))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_46]),c_0_44])).

fof(c_0_52,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_xboole_0(esk3_3(X35,X36,X37))
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) )
      & ( v2_waybel_0(esk3_3(X35,X36,X37),X35)
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) )
      & ( v13_waybel_0(esk3_3(X35,X36,X37),X35)
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) )
      & ( m1_subset_1(esk3_3(X35,X36,X37),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) )
      & ( v2_waybel_7(esk3_3(X35,X36,X37),X35)
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) )
      & ( r1_tarski(X37,esk3_3(X35,X36,X37))
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) )
      & ( r1_subset_1(X36,esk3_3(X35,X36,X37))
        | ~ r1_subset_1(X36,X37)
        | v1_xboole_0(X37)
        | ~ v2_waybel_0(X37,X35)
        | ~ v13_waybel_0(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | v1_xboole_0(X36)
        | ~ v1_waybel_0(X36,X35)
        | ~ v12_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v2_waybel_1(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_7])])])])])])).

fof(c_0_53,negated_conjecture,(
    ! [X56] :
      ( ~ v7_struct_0(esk5_0)
      & v3_orders_2(esk5_0)
      & v4_orders_2(esk5_0)
      & v5_orders_2(esk5_0)
      & v11_waybel_1(esk5_0)
      & v1_lattice3(esk5_0)
      & v2_lattice3(esk5_0)
      & l1_orders_2(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      & v2_waybel_0(esk6_0,esk5_0)
      & v13_waybel_0(esk6_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & ( v1_xboole_0(X56)
        | ~ v2_waybel_0(X56,esk5_0)
        | ~ v13_waybel_0(X56,esk5_0)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ r1_tarski(esk6_0,X56)
        | ~ v3_waybel_7(X56,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_47])])])])])).

fof(c_0_54,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_55,plain,(
    ! [X22,X23] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X22,X23))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22)) )
      & ( v1_waybel_0(k5_waybel_0(X22,X23),X22)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_56,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ v1_yellow_0(X32)
      | ~ l1_orders_2(X32)
      | k5_waybel_0(X32,k3_yellow_0(X32)) = k6_domain_1(u1_struct_0(X32),k3_yellow_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_waybel_4])])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_tarski(X2))
    | ~ r2_hidden(X3,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_50])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k1_tarski(X1),X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_61,plain,
    ( r1_subset_1(X1,esk3_3(X2,X1,X3))
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( v2_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_72,plain,(
    ! [X7] :
      ( ( ~ v2_struct_0(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v3_orders_2(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v5_orders_2(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v1_lattice3(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v2_lattice3(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v3_yellow_0(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v2_waybel_1(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) )
      & ( v10_waybel_1(X7)
        | v2_struct_0(X7)
        | ~ v11_waybel_1(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

cnf(c_0_73,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | k5_waybel_0(X1,k3_yellow_0(X1)) = k6_domain_1(u1_struct_0(X1),k3_yellow_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_76,plain,
    ( k6_domain_1(u1_struct_0(X1),k3_yellow_0(X1)) = k1_tarski(k3_yellow_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_77,plain,(
    ! [X47,X48,X49] :
      ( ~ r2_hidden(X47,X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(X49))
      | ~ v1_xboole_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_78,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X2),X3)
    | ~ r2_hidden(esk4_2(k1_tarski(X2),X3),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_26])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r1_xboole_0(k1_tarski(X2),X3)
    | r2_hidden(esk4_2(X1,k1_tarski(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( r1_subset_1(X1,esk3_3(esk5_0,X1,esk6_0))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_81,plain,
    ( v2_waybel_1(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( v11_waybel_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_69]),c_0_70])])).

cnf(c_0_84,plain,
    ( v1_waybel_0(k5_waybel_0(X1,k3_yellow_0(X1)),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_58])).

cnf(c_0_85,plain,
    ( k5_waybel_0(X1,k3_yellow_0(X1)) = k1_tarski(k3_yellow_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_86,plain,(
    ! [X6] :
      ( ( v1_yellow_0(X6)
        | ~ v3_yellow_0(X6)
        | ~ l1_orders_2(X6) )
      & ( v2_yellow_0(X6)
        | ~ v3_yellow_0(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_87,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v4_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | v12_waybel_0(k5_waybel_0(X20,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_89,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X3),k1_tarski(X1))
    | r1_xboole_0(k1_tarski(X2),k1_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

fof(c_0_90,plain,(
    ! [X26,X27] :
      ( ( ~ r1_subset_1(X26,X27)
        | r1_xboole_0(X26,X27)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27) )
      & ( ~ r1_xboole_0(X26,X27)
        | r1_subset_1(X26,X27)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_91,plain,(
    ! [X52,X53] :
      ( ( ~ v1_subset_1(X53,u1_struct_0(X52))
        | ~ r2_hidden(k3_yellow_0(X52),X53)
        | v1_xboole_0(X53)
        | ~ v2_waybel_0(X53,X52)
        | ~ v13_waybel_0(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v3_orders_2(X52)
        | ~ v4_orders_2(X52)
        | ~ v5_orders_2(X52)
        | ~ v1_yellow_0(X52)
        | ~ l1_orders_2(X52) )
      & ( r2_hidden(k3_yellow_0(X52),X53)
        | v1_subset_1(X53,u1_struct_0(X52))
        | v1_xboole_0(X53)
        | ~ v2_waybel_0(X53,X52)
        | ~ v13_waybel_0(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v3_orders_2(X52)
        | ~ v4_orders_2(X52)
        | ~ v5_orders_2(X52)
        | ~ v1_yellow_0(X52)
        | ~ l1_orders_2(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_7])])])])])).

cnf(c_0_92,negated_conjecture,
    ( r1_subset_1(X1,esk3_3(esk5_0,X1,esk6_0))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_93,plain,
    ( v1_waybel_0(k1_tarski(k3_yellow_0(X1)),X1)
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_94,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_95,plain,
    ( v3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,plain,
    ( r1_xboole_0(k1_tarski(k1_zfmisc_1(X1)),k1_tarski(X2))
    | r1_xboole_0(k1_tarski(X2),k1_tarski(X3))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X4,X3)
    | ~ r2_hidden(X5,X4) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_99,plain,(
    ! [X28,X29] :
      ( v1_xboole_0(X28)
      | v1_xboole_0(X29)
      | ~ r1_subset_1(X28,X29)
      | r1_subset_1(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).

cnf(c_0_100,plain,
    ( r1_subset_1(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(k3_yellow_0(X2),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_yellow_0(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_102,plain,
    ( v13_waybel_0(esk3_3(X1,X2,X3),X1)
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_103,plain,
    ( v2_waybel_0(esk3_3(X1,X2,X3),X1)
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_104,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk6_0)
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_44]),c_0_83])).

cnf(c_0_105,plain,
    ( v1_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_106,plain,
    ( v12_waybel_0(k5_waybel_0(X1,k3_yellow_0(X1)),X1)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_58])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(k1_tarski(X1),k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r1_xboole_0(k1_tarski(k1_zfmisc_1(X2)),k1_tarski(X1))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_62])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(X1)
    | m1_subset_1(esk3_3(esk5_0,X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_109,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_subset_1(X2,X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_110,plain,
    ( r1_subset_1(X1,k1_tarski(X2))
    | v1_xboole_0(X1)
    | r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_29]),c_0_44])).

cnf(c_0_111,plain,
    ( v2_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_waybel_0(X2,X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_101,c_0_40])).

cnf(c_0_112,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_113,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,X1,esk6_0),esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_114,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,X1,esk6_0),esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_115,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk6_0)
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_116,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v12_waybel_0(k1_tarski(k3_yellow_0(X1)),X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_85])).

fof(c_0_117,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | m1_subset_1(k5_waybel_0(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_118,negated_conjecture,
    ( r1_xboole_0(k1_tarski(X1),k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r1_xboole_0(k1_tarski(k1_zfmisc_1(X2)),k1_tarski(X1))
    | ~ v1_xboole_0(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_43]),c_0_71])).

cnf(c_0_119,negated_conjecture,
    ( v1_xboole_0(X1)
    | m1_subset_1(esk3_3(esk5_0,X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_120,plain,
    ( r1_subset_1(k1_tarski(X1),X2)
    | v1_xboole_0(X2)
    | r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_44])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0)
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_63]),c_0_64]),c_0_62]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_122,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,X1,esk6_0),esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_123,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,X1,esk6_0),esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_124,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk6_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_125,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_126,negated_conjecture,
    ( r1_xboole_0(k1_tarski(X1),k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k1_tarski(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X3,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_118])).

cnf(c_0_127,plain,
    ( v2_waybel_7(esk3_3(X1,X2,X3),X1)
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,k1_tarski(X1),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | r2_hidden(X1,esk6_0)
    | ~ v1_waybel_0(k1_tarski(X1),esk5_0)
    | ~ v12_waybel_0(k1_tarski(X1),esk5_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_44]),c_0_71])).

cnf(c_0_129,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_130,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(X1),esk6_0),esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ v1_waybel_0(k1_tarski(X1),esk5_0)
    | ~ v12_waybel_0(k1_tarski(X1),esk5_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_120]),c_0_44]),c_0_71])).

cnf(c_0_131,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(X1),esk6_0),esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ v1_waybel_0(k1_tarski(X1),esk5_0)
    | ~ v12_waybel_0(k1_tarski(X1),esk5_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_120]),c_0_44]),c_0_71])).

cnf(c_0_132,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk6_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_133,plain,
    ( m1_subset_1(k5_waybel_0(X1,k3_yellow_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_58])).

cnf(c_0_134,negated_conjecture,
    ( r1_xboole_0(k1_tarski(X1),k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X1,k1_tarski(k1_zfmisc_1(X2))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_43]),c_0_46]),c_0_44])).

cnf(c_0_135,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,X1,esk6_0),esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_136,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_93]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_129]),c_0_83])).

cnf(c_0_138,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_93]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_129]),c_0_83])).

cnf(c_0_139,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_93]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_129]),c_0_83])).

cnf(c_0_140,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_120]),c_0_71]),c_0_129])).

cnf(c_0_141,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | m1_subset_1(k1_tarski(k3_yellow_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_133,c_0_85])).

cnf(c_0_142,negated_conjecture,
    ( r1_xboole_0(k1_tarski(k1_zfmisc_1(X1)),k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_43]),c_0_46]),c_0_44])).

cnf(c_0_143,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,X1,esk6_0),esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_144,plain,
    ( r1_tarski(X1,esk3_3(X2,X3,X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ r1_subset_1(X3,X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X3,X2)
    | ~ v12_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_145,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v1_xboole_0(esk3_3(esk5_0,X1,esk6_0))
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_146,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_147,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_148,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_149,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_150,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ r2_hidden(X2,k1_tarski(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_142])).

cnf(c_0_151,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(X1),esk6_0),esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ v1_waybel_0(k1_tarski(X1),esk5_0)
    | ~ v12_waybel_0(k1_tarski(X1),esk5_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_120]),c_0_44]),c_0_71])).

cnf(c_0_152,plain,
    ( r1_tarski(X1,esk3_3(X2,k5_waybel_0(X2,k3_yellow_0(X2)),X1))
    | v1_xboole_0(k5_waybel_0(X2,k3_yellow_0(X2)))
    | v1_xboole_0(X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ r1_subset_1(k5_waybel_0(X2,k3_yellow_0(X2)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_133]),c_0_106]),c_0_84]),c_0_73])).

cnf(c_0_153,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r1_subset_1(X1,esk6_0)
    | ~ v1_waybel_0(X1,esk5_0)
    | ~ v1_xboole_0(esk3_3(esk5_0,X1,esk6_0))
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_154,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_116]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_155,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_116]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_156,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_116]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_157,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_158,negated_conjecture,
    ( r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_159,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_160,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(k1_zfmisc_1(X1),k1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_43]),c_0_46]),c_0_44])).

cnf(c_0_161,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_93]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_129]),c_0_83])).

cnf(c_0_162,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_3(esk5_0,k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)))
    | ~ r1_subset_1(k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)),esk6_0)
    | ~ v2_waybel_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_163,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ v1_waybel_0(k1_tarski(X1),esk5_0)
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(X1),esk6_0))
    | ~ v12_waybel_0(k1_tarski(X1),esk5_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_120]),c_0_44]),c_0_71])).

cnf(c_0_164,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_165,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_166,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_167,negated_conjecture,
    ( r1_xboole_0(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_44]),c_0_159])).

cnf(c_0_168,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_41])).

cnf(c_0_169,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_170,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_3(esk5_0,k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)))
    | ~ r1_subset_1(k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_81]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_171,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_93]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_129]),c_0_83])).

cnf(c_0_172,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_141]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_173,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_141]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_174,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_141]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_175,negated_conjecture,
    ( r1_xboole_0(k1_tarski(k3_yellow_0(esk5_0)),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0)) ),
    inference(sr,[status(thm)],[c_0_167,c_0_168])).

cnf(c_0_176,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_116]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_177,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk6_0)
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_85]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_44]),c_0_83])).

cnf(c_0_178,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_179,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_180,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_181,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_182,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ r2_hidden(X1,k1_tarski(k3_yellow_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_175])).

cnf(c_0_183,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_185,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_116]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_186,plain,
    ( r2_hidden(k3_yellow_0(X1),X2)
    | v1_subset_1(X2,u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_187,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_179,c_0_168])).

cnf(c_0_188,negated_conjecture,
    ( v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[c_0_180,c_0_168])).

cnf(c_0_189,negated_conjecture,
    ( v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[c_0_181,c_0_168])).

cnf(c_0_190,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_43]),c_0_46]),c_0_44])).

cnf(c_0_191,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_141]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_192,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,esk5_0)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(esk6_0,X1)
    | ~ v3_waybel_7(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_193,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_120]),c_0_71]),c_0_129])).

cnf(c_0_194,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

fof(c_0_195,plain,(
    ! [X33,X34] :
      ( ( ~ v1_subset_1(X34,u1_struct_0(X33))
        | ~ v2_waybel_7(X34,X33)
        | v3_waybel_7(X34,X33)
        | v1_xboole_0(X34)
        | ~ v2_waybel_0(X34,X33)
        | ~ v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ v11_waybel_1(X33)
        | ~ v1_lattice3(X33)
        | ~ v2_lattice3(X33)
        | ~ l1_orders_2(X33) )
      & ( v1_subset_1(X34,u1_struct_0(X33))
        | ~ v3_waybel_7(X34,X33)
        | v1_xboole_0(X34)
        | ~ v2_waybel_0(X34,X33)
        | ~ v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ v11_waybel_1(X33)
        | ~ v1_lattice3(X33)
        | ~ v2_lattice3(X33)
        | ~ l1_orders_2(X33) )
      & ( v2_waybel_7(X34,X33)
        | ~ v3_waybel_7(X34,X33)
        | v1_xboole_0(X34)
        | ~ v2_waybel_0(X34,X33)
        | ~ v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ v11_waybel_1(X33)
        | ~ v1_lattice3(X33)
        | ~ v2_lattice3(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_waybel_7])])])])])).

cnf(c_0_196,negated_conjecture,
    ( v1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),u1_struct_0(esk5_0))
    | v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_188]),c_0_189]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83]),c_0_190])).

cnf(c_0_197,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_198,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v3_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | ~ v13_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | ~ v2_waybel_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_192,c_0_193])).

cnf(c_0_199,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ v1_yellow_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_141]),c_0_66]),c_0_67]),c_0_68]),c_0_70])]),c_0_83])).

cnf(c_0_200,plain,
    ( v3_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_waybel_7(X1,X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v11_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_195])).

cnf(c_0_201,negated_conjecture,
    ( v1_subset_1(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),u1_struct_0(esk5_0))
    | v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_202,negated_conjecture,
    ( v2_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[c_0_197,c_0_168])).

cnf(c_0_203,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0))
    | ~ v3_waybel_7(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_198,c_0_189])]),c_0_168]),c_0_188]),c_0_187])])).

cnf(c_0_204,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_105]),c_0_82]),c_0_70])]),c_0_83])).

cnf(c_0_205,negated_conjecture,
    ( v1_xboole_0(esk3_3(esk5_0,k1_tarski(k3_yellow_0(esk5_0)),esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_201]),c_0_202]),c_0_188]),c_0_189]),c_0_187]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_82]),c_0_69]),c_0_70])]),c_0_203])).

cnf(c_0_206,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_204,c_0_205])]),c_0_168]),
    [proof]).

%------------------------------------------------------------------------------
