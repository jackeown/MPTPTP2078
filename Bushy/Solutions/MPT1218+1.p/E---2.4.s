%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t54_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 157.51s
% Output     : CNFRefutation 157.51s
% Verified   : 
% Statistics : Number of formulae       :  202 (9718 expanded)
%              Number of clauses        :  153 (3823 expanded)
%              Number of leaves         :   24 (2465 expanded)
%              Depth                    :   32
%              Number of atoms          :  978 (52371 expanded)
%              Number of equality atoms :   33 (3716 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t54_lattices)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t23_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',cc1_lattices)).

fof(dt_l2_lattices,axiom,(
    ! [X1] :
      ( l2_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_l2_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_l3_lattices)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t5_subset)).

fof(rc14_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v18_lattices(X2,X1)
          & v19_lattices(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',rc14_lattices)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',existence_m1_subset_1)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',redefinition_k4_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',redefinition_r3_lattices)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',d3_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',d23_lattices)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_k2_struct_0)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_k2_lattices)).

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',reflexivity_r3_lattices)).

fof(dt_l1_lattices,axiom,(
    ! [X1] :
      ( l1_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_l1_lattices)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t1_subset)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',commutativity_k4_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',d22_lattices)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t7_boole)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t8_subset_1)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_k4_lattices)).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
    ! [X71,X72,X73] :
      ( ~ r2_hidden(X71,X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(X73))
      | m1_subset_1(X71,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v18_lattices(esk2_0,esk1_0)
    & v19_lattices(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & esk2_0 != k2_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_27,plain,(
    ! [X64,X65,X66] :
      ( v2_struct_0(X64)
      | ~ v6_lattices(X64)
      | ~ v8_lattices(X64)
      | ~ l3_lattices(X64)
      | ~ m1_subset_1(X65,u1_struct_0(X64))
      | ~ m1_subset_1(X66,u1_struct_0(X64))
      | r1_lattices(X64,k4_lattices(X64,X65,X66),X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X86] :
      ( ( ~ v2_struct_0(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) )
      & ( v4_lattices(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) )
      & ( v5_lattices(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) )
      & ( v6_lattices(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) )
      & ( v7_lattices(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) )
      & ( v8_lattices(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) )
      & ( v9_lattices(X86)
        | v2_struct_0(X86)
        | ~ v10_lattices(X86)
        | ~ l3_lattices(X86) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_35,plain,(
    ! [X37] :
      ( ~ l2_lattices(X37)
      | l1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l2_lattices])])).

fof(c_0_36,plain,(
    ! [X38] :
      ( ( l1_lattices(X38)
        | ~ l3_lattices(X38) )
      & ( l2_lattices(X38)
        | ~ l3_lattices(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_38,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_40,plain,(
    ! [X74,X75,X76] :
      ( ~ r2_hidden(X74,X75)
      | ~ m1_subset_1(X75,k1_zfmisc_1(X76))
      | ~ v1_xboole_0(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_41,plain,(
    ! [X87] :
      ( ( m1_subset_1(esk14_1(X87),k1_zfmisc_1(u1_struct_0(X87)))
        | v2_struct_0(X87)
        | ~ v10_lattices(X87)
        | ~ l3_lattices(X87) )
      & ( ~ v1_xboole_0(esk14_1(X87))
        | v2_struct_0(X87)
        | ~ v10_lattices(X87)
        | ~ l3_lattices(X87) )
      & ( v18_lattices(esk14_1(X87),X87)
        | v2_struct_0(X87)
        | ~ v10_lattices(X87)
        | ~ l3_lattices(X87) )
      & ( v19_lattices(esk14_1(X87),X87)
        | v2_struct_0(X87)
        | ~ v10_lattices(X87)
        | ~ l3_lattices(X87) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc14_lattices])])])])])).

fof(c_0_42,plain,(
    ! [X67,X68] :
      ( ~ m1_subset_1(X67,X68)
      | v1_xboole_0(X68)
      | r2_hidden(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_43,plain,(
    ! [X44] : m1_subset_1(esk11_1(X44),X44) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_44,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v6_lattices(X50)
      | ~ l1_lattices(X50)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | ~ m1_subset_1(X52,u1_struct_0(X50))
      | k4_lattices(X50,X51,X52) = k2_lattices(X50,X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_45,plain,(
    ! [X53,X54,X55] :
      ( ( ~ r3_lattices(X53,X54,X55)
        | r1_lattices(X53,X54,X55)
        | v2_struct_0(X53)
        | ~ v6_lattices(X53)
        | ~ v8_lattices(X53)
        | ~ v9_lattices(X53)
        | ~ l3_lattices(X53)
        | ~ m1_subset_1(X54,u1_struct_0(X53))
        | ~ m1_subset_1(X55,u1_struct_0(X53)) )
      & ( ~ r1_lattices(X53,X54,X55)
        | r3_lattices(X53,X54,X55)
        | v2_struct_0(X53)
        | ~ v6_lattices(X53)
        | ~ v8_lattices(X53)
        | ~ v9_lattices(X53)
        | ~ l3_lattices(X53)
        | ~ m1_subset_1(X54,u1_struct_0(X53))
        | ~ m1_subset_1(X55,u1_struct_0(X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_46,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | k2_struct_0(X24) = u1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_50,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk14_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk11_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
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

cnf(c_0_57,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( l1_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

fof(c_0_60,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ v19_lattices(X19,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r3_lattices(X18,X20,X21)
        | ~ r2_hidden(X20,X19)
        | r2_hidden(X21,X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk5_2(X18,X19),u1_struct_0(X18))
        | v19_lattices(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk6_2(X18,X19),u1_struct_0(X18))
        | v19_lattices(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( r3_lattices(X18,esk5_2(X18,X19),esk6_2(X18,X19))
        | v19_lattices(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( r2_hidden(esk5_2(X18,X19),X19)
        | v19_lattices(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( ~ r2_hidden(esk6_2(X18,X19),X19)
        | v19_lattices(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d23_lattices])])])])])])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ r2_hidden(X2,esk14_1(X1))
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( r2_hidden(esk11_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk14_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X1,X2)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_31]),c_0_33])).

cnf(c_0_65,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_66,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X3,k2_struct_0(X1))
    | ~ m1_subset_1(X2,k2_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_68,plain,
    ( v19_lattices(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
    | v19_lattices(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

fof(c_0_71,plain,(
    ! [X28] :
      ( ~ l1_struct_0(X28)
      | m1_subset_1(k2_struct_0(X28),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_72,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ l1_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | m1_subset_1(k2_lattices(X25,X26,X27),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

cnf(c_0_73,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X1,X2)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_32])])).

cnf(c_0_74,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_32])]),c_0_33])).

cnf(c_0_75,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_76,plain,(
    ! [X56,X57,X58] :
      ( v2_struct_0(X56)
      | ~ v6_lattices(X56)
      | ~ v8_lattices(X56)
      | ~ v9_lattices(X56)
      | ~ l3_lattices(X56)
      | ~ m1_subset_1(X57,u1_struct_0(X56))
      | ~ m1_subset_1(X58,u1_struct_0(X56))
      | r3_lattices(X56,X57,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

cnf(c_0_77,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_78,plain,
    ( v19_lattices(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(esk6_2(X2,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2)))
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_57]),c_0_58])).

cnf(c_0_79,plain,
    ( r2_hidden(esk6_2(X1,X2),u1_struct_0(X1))
    | v19_lattices(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_69]),c_0_70])).

cnf(c_0_80,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

fof(c_0_83,plain,(
    ! [X36] :
      ( ~ l1_lattices(X36)
      | l1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_lattices])])).

cnf(c_0_84,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v8_lattices(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r3_lattices(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v19_lattices(X2,X3)
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_77,c_0_28])).

cnf(c_0_87,plain,
    ( v19_lattices(u1_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_57])).

cnf(c_0_89,plain,
    ( r2_hidden(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X1,X2)
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_57])).

cnf(c_0_91,plain,
    ( l1_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_29])).

cnf(c_0_93,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ l1_struct_0(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_38]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0)))
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r3_lattices(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X3)))
    | ~ m1_subset_1(X1,k2_struct_0(X3))
    | ~ v19_lattices(X2,X3)
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_57]),c_0_58])).

cnf(c_0_97,plain,
    ( v19_lattices(k2_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_57]),c_0_88]),c_0_58])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,X2),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_33]),c_0_31]),c_0_91]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_58]),c_0_32])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,X2),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_90]),c_0_33]),c_0_31]),c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(X1,k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_75]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,k2_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X3,X1)
    | ~ r2_hidden(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X1,k2_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_88]),c_0_97]),c_0_58])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_57]),c_0_91])).

cnf(c_0_106,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_57]),c_0_91])).

cnf(c_0_108,plain,
    ( r2_hidden(X1,k2_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X3,X1)
    | ~ r2_hidden(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_80]),c_0_97]),c_0_58])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_101]),c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_38]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r3_lattices(esk1_0,k4_lattices(esk1_0,X2,X3),X1)
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_112,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_114,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_58]),c_0_32])])).

cnf(c_0_117,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_31])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_65]),c_0_32])])).

cnf(c_0_120,plain,
    ( m1_subset_1(k2_lattices(X1,X2,X3),k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X3,k2_struct_0(X1))
    | ~ m1_subset_1(X2,k2_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_57]),c_0_91])).

fof(c_0_121,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | m1_subset_1(X62,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_31])).

cnf(c_0_123,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_62]),c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X2)
    | ~ r1_lattices(esk1_0,X1,X2)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k2_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_33])).

cnf(c_0_126,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

fof(c_0_128,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v6_lattices(X9)
      | ~ l1_lattices(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k4_lattices(X9,X10,X11) = k4_lattices(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_129,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X2)
    | ~ r1_lattices(esk1_0,X1,X2)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_75]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k2_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_65]),c_0_32])])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_132,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X2)
    | ~ r1_lattices(esk1_0,X1,X2)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_38]),c_0_32]),c_0_39])]),c_0_33])).

fof(c_0_134,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v18_lattices(X13,X12)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r3_lattices(X12,X14,X15)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X14,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk3_2(X12,X13),u1_struct_0(X12))
        | v18_lattices(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk4_2(X12,X13),u1_struct_0(X12))
        | v18_lattices(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( r3_lattices(X12,esk3_2(X12,X13),esk4_2(X12,X13))
        | v18_lattices(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( r2_hidden(esk4_2(X12,X13),X13)
        | v18_lattices(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X13),X13)
        | v18_lattices(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattices])])])])])])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(k2_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ r2_hidden(X3,esk2_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_136,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ r2_hidden(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_80])).

fof(c_0_137,plain,(
    ! [X78,X79] :
      ( ~ r2_hidden(X78,X79)
      | ~ v1_xboole_0(X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_138,plain,
    ( k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X3,k2_struct_0(X1))
    | ~ m1_subset_1(X2,k2_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_57]),c_0_91])).

cnf(c_0_139,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X2)
    | ~ r1_lattices(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_140,negated_conjecture,
    ( v19_lattices(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_141,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(k2_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1),k2_struct_0(esk1_0))
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_54])).

cnf(c_0_143,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X1,X2)
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_136])).

cnf(c_0_144,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_145,negated_conjecture,
    ( k4_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X2,X1)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_131]),c_0_33])).

cnf(c_0_146,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X2)
    | ~ r1_lattices(esk1_0,X1,X2)
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_57])).

cnf(c_0_147,plain,
    ( r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X3,k2_struct_0(X1))
    | ~ m1_subset_1(X2,k2_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_57]),c_0_58])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_29]),c_0_140]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_149,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r3_lattices(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v18_lattices(X2,X3)
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_141,c_0_28])).

cnf(c_0_150,negated_conjecture,
    ( v18_lattices(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(k2_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1),k2_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_62]),c_0_118])).

cnf(c_0_152,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X1,X2)
    | ~ r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_58]),c_0_32])])).

cnf(c_0_153,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_127])).

cnf(c_0_154,negated_conjecture,
    ( k4_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X2,X1)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_65]),c_0_32])])).

cnf(c_0_155,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v8_lattices(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_32])]),c_0_33]),c_0_131])).

cnf(c_0_156,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_57])).

cnf(c_0_157,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_29]),c_0_150]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_158,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1),k2_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_151])).

cnf(c_0_159,negated_conjecture,
    ( k2_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1) = k4_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_62]),c_0_153])).

cnf(c_0_160,negated_conjecture,
    ( k4_lattices(esk1_0,X1,X2) = k4_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_161,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ l1_struct_0(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_38]),c_0_32]),c_0_39])]),c_0_33])).

fof(c_0_162,plain,(
    ! [X82,X83,X84] :
      ( ( m1_subset_1(esk13_3(X82,X83,X84),X82)
        | X83 = X84
        | ~ m1_subset_1(X84,k1_zfmisc_1(X82))
        | ~ m1_subset_1(X83,k1_zfmisc_1(X82)) )
      & ( ~ r2_hidden(esk13_3(X82,X83,X84),X83)
        | ~ r2_hidden(esk13_3(X82,X83,X84),X84)
        | X83 = X84
        | ~ m1_subset_1(X84,k1_zfmisc_1(X82))
        | ~ m1_subset_1(X83,k1_zfmisc_1(X82)) )
      & ( r2_hidden(esk13_3(X82,X83,X84),X83)
        | r2_hidden(esk13_3(X82,X83,X84),X84)
        | X83 = X84
        | ~ m1_subset_1(X84,k1_zfmisc_1(X82))
        | ~ m1_subset_1(X83,k1_zfmisc_1(X82)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_163,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_58]),c_0_32])])).

cnf(c_0_164,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ r3_lattices(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_57])).

cnf(c_0_165,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1),k2_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_166,negated_conjecture,
    ( k4_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1) = k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_160,c_0_54])).

cnf(c_0_167,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_58]),c_0_32])])).

cnf(c_0_168,plain,
    ( r2_hidden(esk13_3(X1,X2,X3),X2)
    | r2_hidden(esk13_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_162])).

fof(c_0_169,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v6_lattices(X33)
      | ~ l1_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | m1_subset_1(k4_lattices(X33,X34,X35),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_170,negated_conjecture,
    ( r2_hidden(esk11_1(k2_struct_0(esk1_0)),esk2_0)
    | ~ r3_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_54])).

cnf(c_0_171,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ r2_hidden(k4_lattices(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_131])).

cnf(c_0_172,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_58]),c_0_32])])).

cnf(c_0_173,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),k2_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_166])).

cnf(c_0_174,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),k2_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_175,plain,
    ( X1 = k2_struct_0(X2)
    | r2_hidden(esk13_3(k2_struct_0(X2),X1,k2_struct_0(X2)),k2_struct_0(X2))
    | r2_hidden(esk13_3(k2_struct_0(X2),X1,k2_struct_0(X2)),X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_168,c_0_88])).

cnf(c_0_176,negated_conjecture,
    ( esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_177,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_169])).

cnf(c_0_178,negated_conjecture,
    ( r2_hidden(esk11_1(k2_struct_0(esk1_0)),esk2_0)
    | ~ r2_hidden(k4_lattices(esk1_0,esk11_1(k2_struct_0(esk1_0)),X1),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_54])])).

cnf(c_0_179,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),esk2_0)
    | ~ r3_lattices(esk1_0,k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_180,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_173]),c_0_54])])).

cnf(c_0_181,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_136])).

cnf(c_0_182,plain,
    ( X2 = X3
    | ~ r2_hidden(esk13_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk13_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_162])).

cnf(c_0_183,negated_conjecture,
    ( r2_hidden(esk13_3(k2_struct_0(esk1_0),esk2_0,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_94]),c_0_176]),c_0_127])).

cnf(c_0_184,plain,
    ( m1_subset_1(k4_lattices(X1,X2,X3),k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X3,k2_struct_0(X1))
    | ~ m1_subset_1(X2,k2_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_57]),c_0_91])).

cnf(c_0_185,negated_conjecture,
    ( r2_hidden(esk11_1(k2_struct_0(esk1_0)),esk2_0)
    | ~ r2_hidden(k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_178,c_0_166])).

cnf(c_0_186,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_179,c_0_180])).

cnf(c_0_187,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r3_lattices(esk1_0,X2,X1)
    | ~ r2_hidden(X1,k2_struct_0(esk1_0))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_58]),c_0_32])])).

cnf(c_0_188,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(esk13_3(k2_struct_0(esk1_0),esk2_0,k2_struct_0(esk1_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_183]),c_0_176]),c_0_94]),c_0_88])).

cnf(c_0_189,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,X2),esk2_0)
    | ~ r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X3)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_184]),c_0_33])).

cnf(c_0_190,negated_conjecture,
    ( r3_lattices(esk1_0,k4_lattices(esk1_0,X1,X2),X1)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_184]),c_0_33]),c_0_131])).

cnf(c_0_191,negated_conjecture,
    ( r2_hidden(esk11_1(k2_struct_0(esk1_0)),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_185,c_0_186])).

cnf(c_0_192,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ r3_lattices(esk1_0,X1,esk13_3(k2_struct_0(esk1_0),esk2_0,k2_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_183]),c_0_188])).

cnf(c_0_193,negated_conjecture,
    ( m1_subset_1(esk13_3(k2_struct_0(esk1_0),esk2_0,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_183])).

cnf(c_0_194,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,X2),esk2_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X2,k2_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_131])).

cnf(c_0_195,plain,
    ( k4_lattices(X1,X2,esk11_1(k2_struct_0(X1))) = k4_lattices(X1,esk11_1(k2_struct_0(X1)),X2)
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_54])).

cnf(c_0_196,negated_conjecture,
    ( r2_hidden(esk11_1(k2_struct_0(esk1_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_62]),c_0_118])).

cnf(c_0_197,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(k4_lattices(esk1_0,esk13_3(k2_struct_0(esk1_0),esk2_0,k2_struct_0(esk1_0)),X1),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_171]),c_0_193])).

cnf(c_0_198,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,esk11_1(k2_struct_0(esk1_0))),esk2_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_195]),c_0_196])]),c_0_33])).

cnf(c_0_199,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_198]),c_0_196])]),c_0_193]),c_0_91])).

cnf(c_0_200,negated_conjecture,
    ( ~ l1_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_50]),c_0_32]),c_0_39])]),c_0_33])).

cnf(c_0_201,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_65]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
