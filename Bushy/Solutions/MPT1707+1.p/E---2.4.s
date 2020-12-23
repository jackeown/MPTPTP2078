%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t16_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 148 expanded)
%              Number of clauses        :   40 (  56 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  275 (1157 expanded)
%              Number of equality atoms :   26 ( 144 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',d3_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',t7_boole)).

fof(d2_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_pre_topc(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X4 = k1_tsep_1(X1,X2,X3)
                  <=> u1_struct_0(X4) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',d2_tsep_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',dt_k1_tsep_1)).

fof(t16_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ~ ( ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => X5 != X4 )
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => X5 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',t16_tmap_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',existence_m1_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',fc2_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',dt_l1_pre_topc)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t16_tmap_1.p',t1_subset)).

fof(c_0_11,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(X30,X27)
        | r2_hidden(X30,X28)
        | X29 != k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X31,X27)
        | r2_hidden(X31,X29)
        | X29 != k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(esk5_3(X32,X33,X34),X32)
        | ~ r2_hidden(esk5_3(X32,X33,X34),X34)
        | X34 = k2_xboole_0(X32,X33) )
      & ( ~ r2_hidden(esk5_3(X32,X33,X34),X33)
        | ~ r2_hidden(esk5_3(X32,X33,X34),X34)
        | X34 = k2_xboole_0(X32,X33) )
      & ( r2_hidden(esk5_3(X32,X33,X34),X34)
        | r2_hidden(esk5_3(X32,X33,X34),X32)
        | r2_hidden(esk5_3(X32,X33,X34),X33)
        | X34 = k2_xboole_0(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X81,X82] :
      ( ~ r2_hidden(X81,X82)
      | ~ v1_xboole_0(X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X26 != k1_tsep_1(X23,X24,X25)
        | u1_struct_0(X26) = k2_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( u1_struct_0(X26) != k2_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | X26 = k1_tsep_1(X23,X24,X25)
        | v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_15,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v2_struct_0(k1_tsep_1(X38,X39,X40))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38) )
      & ( v1_pre_topc(k1_tsep_1(X38,X39,X40))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38) )
      & ( m1_pre_topc(k1_tsep_1(X38,X39,X40),X38)
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                   => ~ ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => X5 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => X5 != X4 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tmap_1])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( u1_struct_0(X1) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k1_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X70,X71] :
      ( ~ m1_subset_1(X70,X71)
      | v1_xboole_0(X71)
      | r2_hidden(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_24,negated_conjecture,(
    ! [X10,X11] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk1_0)
      & m1_subset_1(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
      & ( ~ m1_subset_1(X10,u1_struct_0(esk2_0))
        | X10 != esk4_0 )
      & ( ~ m1_subset_1(X11,u1_struct_0(esk3_0))
        | X11 != esk4_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k2_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X52] : m1_subset_1(esk9_1(X52),X52) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ r2_hidden(X4,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | r2_hidden(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_39])).

fof(c_0_43,plain,(
    ! [X85] :
      ( v2_struct_0(X85)
      | ~ l1_struct_0(X85)
      | ~ v1_xboole_0(u1_struct_0(X85)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | r2_hidden(X1,u1_struct_0(X3))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,u1_struct_0(k1_tsep_1(X4,X2,X3)))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ l1_pre_topc(X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | l1_pre_topc(X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37]),c_0_38])).

fof(c_0_49,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | l1_struct_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_50,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_51,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | m1_subset_1(X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0))
    | r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_38])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_35])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0))
    | m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    | m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | X1 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_60,c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
