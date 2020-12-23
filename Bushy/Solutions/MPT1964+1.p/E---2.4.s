%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t13_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:03 EDT 2019

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 205 expanded)
%              Number of clauses        :   27 (  76 expanded)
%              Number of leaves         :    8 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  260 (1247 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_waybel_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(k12_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',t41_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',t4_subset)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',fc7_yellow_1)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',cc8_waybel_1)).

fof(fc1_waybel_7,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v11_waybel_1(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',fc1_waybel_7)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',dt_k3_yellow_1)).

fof(t17_yellow_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
            & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',t17_yellow_1)).

fof(t13_waybel_7,conjecture,(
    ! [X1,X2] :
      ( ( v13_waybel_0(X2,k3_yellow_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
     => ( v2_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X2)
              & r2_hidden(X4,X2) )
           => r2_hidden(k3_xboole_0(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t13_waybel_7.p',t13_waybel_7)).

fof(c_0_8,plain,(
    ! [X68,X69,X70,X71] :
      ( ( ~ v2_waybel_0(X69,X68)
        | ~ m1_subset_1(X70,u1_struct_0(X68))
        | ~ m1_subset_1(X71,u1_struct_0(X68))
        | ~ r2_hidden(X70,X69)
        | ~ r2_hidden(X71,X69)
        | r2_hidden(k12_lattice3(X68,X70,X71),X69)
        | ~ v13_waybel_0(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v5_orders_2(X68)
        | ~ v2_lattice3(X68)
        | ~ l1_orders_2(X68) )
      & ( m1_subset_1(esk8_2(X68,X69),u1_struct_0(X68))
        | v2_waybel_0(X69,X68)
        | ~ v13_waybel_0(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v5_orders_2(X68)
        | ~ v2_lattice3(X68)
        | ~ l1_orders_2(X68) )
      & ( m1_subset_1(esk9_2(X68,X69),u1_struct_0(X68))
        | v2_waybel_0(X69,X68)
        | ~ v13_waybel_0(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v5_orders_2(X68)
        | ~ v2_lattice3(X68)
        | ~ l1_orders_2(X68) )
      & ( r2_hidden(esk8_2(X68,X69),X69)
        | v2_waybel_0(X69,X68)
        | ~ v13_waybel_0(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v5_orders_2(X68)
        | ~ v2_lattice3(X68)
        | ~ l1_orders_2(X68) )
      & ( r2_hidden(esk9_2(X68,X69),X69)
        | v2_waybel_0(X69,X68)
        | ~ v13_waybel_0(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v5_orders_2(X68)
        | ~ v2_lattice3(X68)
        | ~ l1_orders_2(X68) )
      & ( ~ r2_hidden(k12_lattice3(X68,esk8_2(X68,X69),esk9_2(X68,X69)),X69)
        | v2_waybel_0(X69,X68)
        | ~ v13_waybel_0(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v5_orders_2(X68)
        | ~ v2_lattice3(X68)
        | ~ l1_orders_2(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_waybel_0])])])])])).

fof(c_0_9,plain,(
    ! [X74,X75,X76] :
      ( ~ r2_hidden(X74,X75)
      | ~ m1_subset_1(X75,k1_zfmisc_1(X76))
      | m1_subset_1(X74,X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,plain,(
    ! [X87] :
      ( ~ v2_struct_0(k3_yellow_1(X87))
      & v1_orders_2(k3_yellow_1(X87))
      & v3_orders_2(k3_yellow_1(X87))
      & v4_orders_2(k3_yellow_1(X87))
      & v5_orders_2(k3_yellow_1(X87)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_11,plain,(
    ! [X85] :
      ( ( ~ v2_struct_0(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v3_orders_2(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v4_orders_2(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v5_orders_2(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v1_lattice3(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v2_lattice3(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v3_yellow_0(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v2_waybel_1(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) )
      & ( v10_waybel_1(X85)
        | v2_struct_0(X85)
        | ~ v11_waybel_1(X85)
        | ~ l1_orders_2(X85) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

fof(c_0_12,plain,(
    ! [X86] :
      ( v1_orders_2(k3_yellow_1(X86))
      & v11_waybel_1(k3_yellow_1(X86)) ) ),
    inference(variable_rename,[status(thm)],[fc1_waybel_7])).

fof(c_0_13,plain,(
    ! [X38] :
      ( v1_orders_2(k3_yellow_1(X38))
      & l1_orders_2(k3_yellow_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

cnf(c_0_14,plain,
    ( r2_hidden(k12_lattice3(X2,X3,X4),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X57,X58,X59] :
      ( ( k13_lattice3(k3_yellow_1(X57),X58,X59) = k2_xboole_0(X58,X59)
        | ~ m1_subset_1(X59,u1_struct_0(k3_yellow_1(X57)))
        | ~ m1_subset_1(X58,u1_struct_0(k3_yellow_1(X57))) )
      & ( k12_lattice3(k3_yellow_1(X57),X58,X59) = k3_xboole_0(X58,X59)
        | ~ m1_subset_1(X59,u1_struct_0(k3_yellow_1(X57)))
        | ~ m1_subset_1(X58,u1_struct_0(k3_yellow_1(X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_yellow_1])])])])).

cnf(c_0_17,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v11_waybel_1(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v13_waybel_0(X2,k3_yellow_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
       => ( v2_waybel_0(X2,k3_yellow_1(X1))
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2) )
             => r2_hidden(k3_xboole_0(X3,X4),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_waybel_7])).

cnf(c_0_22,plain,
    ( r2_hidden(k12_lattice3(X1,X2,X3),X4)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X2,X4)
    | ~ v2_waybel_0(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X4,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_23,plain,
    ( k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( v2_lattice3(k3_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

fof(c_0_26,negated_conjecture,(
    ! [X9,X10] :
      ( v13_waybel_0(esk2_0,k3_yellow_1(esk1_0))
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0))))
      & ( r2_hidden(esk3_0,esk2_0)
        | ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) )
      & ( r2_hidden(esk4_0,esk2_0)
        | ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) )
      & ( ~ r2_hidden(k3_xboole_0(esk3_0,esk4_0),esk2_0)
        | ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) )
      & ( v2_waybel_0(esk2_0,k3_yellow_1(esk1_0))
        | ~ r2_hidden(X9,esk2_0)
        | ~ r2_hidden(X10,esk2_0)
        | r2_hidden(k3_xboole_0(X9,X10),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])])).

cnf(c_0_27,plain,
    ( v2_waybel_0(X2,X1)
    | ~ r2_hidden(k12_lattice3(X1,esk8_2(X1,X2),esk9_2(X1,X2)),X2)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),X3)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ v2_waybel_0(X3,k3_yellow_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X4))))
    | ~ v13_waybel_0(X3,k3_yellow_1(X4)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_20])]),c_0_25])]),c_0_15]),c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(esk1_0))
    | r2_hidden(k3_xboole_0(X1,X2),esk2_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v2_waybel_0(X1,k3_yellow_1(X2))
    | ~ r2_hidden(k3_xboole_0(esk8_2(k3_yellow_1(X2),X1),esk9_2(k3_yellow_1(X2),X1)),X1)
    | ~ m1_subset_1(esk9_2(k3_yellow_1(X2),X1),u1_struct_0(k3_yellow_1(X2)))
    | ~ m1_subset_1(esk8_2(k3_yellow_1(X2),X1),u1_struct_0(k3_yellow_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
    | ~ v13_waybel_0(X1,k3_yellow_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24]),c_0_20])]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k3_xboole_0(X1,X2),esk2_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(X1))
    | ~ r2_hidden(esk9_2(k3_yellow_1(X1),esk2_0),esk2_0)
    | ~ r2_hidden(esk8_2(k3_yellow_1(X1),esk2_0),esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(esk2_0,k3_yellow_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15]),c_0_15])).

cnf(c_0_35,plain,
    ( r2_hidden(esk9_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(X1))
    | ~ r2_hidden(esk8_2(k3_yellow_1(X1),esk2_0),esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(esk2_0,k3_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25]),c_0_24]),c_0_20])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k3_xboole_0(esk3_0,esk4_0),esk2_0)
    | ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(esk2_0,k3_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_24]),c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_30])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
