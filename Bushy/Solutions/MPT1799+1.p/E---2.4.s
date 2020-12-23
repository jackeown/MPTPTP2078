%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t115_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:04 EDT 2019

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   40 (  81 expanded)
%              Number of clauses        :   25 (  30 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  278 ( 607 expanded)
%              Number of equality atoms :   32 (  57 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t105_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t105_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',d11_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',dt_k8_tmap_1)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t16_tsep_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',dt_k6_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t1_tsep_1)).

fof(t115_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
             => ( u1_struct_0(X3) = u1_struct_0(X2)
               => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                  & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t115_tmap_1)).

fof(c_0_7,plain,(
    ! [X76,X77,X78] :
      ( v2_struct_0(X76)
      | ~ v2_pre_topc(X76)
      | ~ l1_pre_topc(X76)
      | ~ m1_subset_1(X77,k1_zfmisc_1(u1_struct_0(X76)))
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X76,X77))))
      | X78 != X77
      | v3_pre_topc(X78,k6_tmap_1(X76,X77)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X24 != k8_tmap_1(X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | X25 != u1_struct_0(X23)
        | X24 = k6_tmap_1(X22,X25)
        | ~ v1_pre_topc(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk4_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))
        | X24 = k8_tmap_1(X22,X23)
        | ~ v1_pre_topc(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( esk4_3(X22,X23,X24) = u1_struct_0(X23)
        | X24 = k8_tmap_1(X22,X23)
        | ~ v1_pre_topc(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( X24 != k6_tmap_1(X22,esk4_3(X22,X23,X24))
        | X24 = k8_tmap_1(X22,X23)
        | ~ v1_pre_topc(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_9,plain,(
    ! [X36,X37] :
      ( ( v1_pre_topc(k8_tmap_1(X36,X37))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_pre_topc(X37,X36) )
      & ( v2_pre_topc(k8_tmap_1(X36,X37))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_pre_topc(X37,X36) )
      & ( l1_pre_topc(k8_tmap_1(X36,X37))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_pre_topc(X37,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_10,plain,(
    ! [X79,X80,X81] :
      ( ( ~ v1_tsep_1(X80,X79)
        | ~ m1_pre_topc(X80,X79)
        | v3_pre_topc(X81,X79)
        | X81 != u1_struct_0(X80)
        | ~ m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X79)))
        | ~ m1_pre_topc(X80,X79)
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79) )
      & ( v1_tsep_1(X80,X79)
        | ~ v3_pre_topc(X81,X79)
        | X81 != u1_struct_0(X80)
        | ~ m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X79)))
        | ~ m1_pre_topc(X80,X79)
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79) )
      & ( m1_pre_topc(X80,X79)
        | ~ v3_pre_topc(X81,X79)
        | X81 != u1_struct_0(X80)
        | ~ m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X79)))
        | ~ m1_pre_topc(X80,X79)
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X34,X35] :
      ( ( v1_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( v2_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( l1_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_13,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X85,X86] :
      ( ~ l1_pre_topc(X85)
      | ~ m1_pre_topc(X86,X85)
      | m1_subset_1(u1_struct_0(X86),k1_zfmisc_1(u1_struct_0(X85))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
               => ( u1_struct_0(X3) = u1_struct_0(X2)
                 => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                    & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_tmap_1])).

cnf(c_0_19,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v3_pre_topc(X1,k6_tmap_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,X3)
    | v2_struct_0(X1)
    | X3 != u1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0))
    & u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    & ( ~ v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))
      | ~ m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_26,plain,
    ( v1_tsep_1(X1,k6_tmap_1(X2,X3))
    | v2_struct_0(X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X2,X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,k6_tmap_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))
    | ~ m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v1_tsep_1(X1,k8_tmap_1(X2,X3))
    | v2_struct_0(X2)
    | u1_struct_0(X3) != u1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | ~ m1_pre_topc(X1,k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( v1_tsep_1(X1,k8_tmap_1(X2,esk2_0))
    | v2_struct_0(X2)
    | u1_struct_0(esk2_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,k8_tmap_1(X2,esk2_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(X2,esk2_0))
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28]),c_0_30]),c_0_35]),c_0_36]),c_0_37])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
