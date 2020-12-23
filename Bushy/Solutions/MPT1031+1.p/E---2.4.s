%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t136_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:30 EDT 2019

% Result     : Theorem 284.48s
% Output     : CNFRefutation 284.48s
% Verified   : 
% Statistics : Number of formulae       :  106 (2190 expanded)
%              Number of clauses        :   73 ( 807 expanded)
%              Number of leaves         :   17 ( 541 expanded)
%              Depth                    :   17
%              Number of atoms          :  457 (20391 expanded)
%              Number of equality atoms :   42 (3707 expanded)
%              Maximal formula depth    :   36 (   5 average)
%              Maximal clause size      :  140 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t136_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ? [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                  & k1_funct_1(X4,X5) != k1_funct_1(X3,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t136_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',redefinition_k1_relset_1)).

fof(s5_funct_2__e3_154_1_2__funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ( r2_hidden(X4,X1)
           => ( ( r2_hidden(X4,k1_relset_1(X1,X2,X3))
               => r2_hidden(k1_funct_1(X3,X4),X2) )
              & ( ~ r2_hidden(X4,k1_relset_1(X1,X2,X3))
               => r2_hidden(o_1_1_funct_2(X2),X2) ) ) )
       => ? [X4] :
            ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & ! [X5] :
                ( r2_hidden(X5,X1)
               => ( ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                   => k1_funct_1(X4,X5) = k1_funct_1(X3,X5) )
                  & ( ~ r2_hidden(X5,k1_relset_1(X1,X2,X3))
                   => k1_funct_1(X4,X5) = o_1_1_funct_2(X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',s5_funct_2__e3_154_1_2__funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',cc1_relset_1)).

fof(t27_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,k1_relat_1(X3))
       => r2_hidden(k1_funct_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t27_partfun1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t1_subset)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',dt_k1_relset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t7_boole)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t4_subset)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',cc1_funct_2)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',cc1_partfun1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t2_subset)).

fof(dt_o_1_1_funct_2,axiom,(
    ! [X1] : m1_subset_1(o_1_1_funct_2(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',dt_o_1_1_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t136_funct_2.p',d2_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
            & ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ? [X5] :
                    ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                    & k1_funct_1(X4,X5) != k1_funct_1(X3,X5) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t136_funct_2])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,negated_conjecture,(
    ! [X9] :
      ( v1_funct_1(esk3_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( esk2_0 != k1_xboole_0
        | esk1_0 = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X9),k1_relset_1(esk1_0,esk2_0,esk3_0))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,esk1_0,esk2_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) )
      & ( k1_funct_1(X9,esk4_1(X9)) != k1_funct_1(esk3_0,esk4_1(X9))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,esk1_0,esk2_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X27] :
      ( ( v1_funct_1(esk7_3(X22,X23,X24))
        | r2_hidden(esk6_3(X22,X23,X24),X22)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(esk7_3(X22,X23,X24),X22,X23)
        | r2_hidden(esk6_3(X22,X23,X24),X22)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(esk7_3(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | r2_hidden(esk6_3(X22,X23,X24),X22)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = k1_funct_1(X24,X27)
        | ~ r2_hidden(X27,X22)
        | r2_hidden(esk6_3(X22,X23,X24),X22)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = o_1_1_funct_2(X23)
        | ~ r2_hidden(X27,X22)
        | r2_hidden(esk6_3(X22,X23,X24),X22)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_1(esk7_3(X22,X23,X24))
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(esk7_3(X22,X23,X24),X22,X23)
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(esk7_3(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = k1_funct_1(X24,X27)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = o_1_1_funct_2(X23)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_1(esk7_3(X22,X23,X24))
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(esk7_3(X22,X23,X24),X22,X23)
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(esk7_3(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = k1_funct_1(X24,X27)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = o_1_1_funct_2(X23)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_1(esk7_3(X22,X23,X24))
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(esk7_3(X22,X23,X24),X22,X23)
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(esk7_3(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = k1_funct_1(X24,X27)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = o_1_1_funct_2(X23)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(esk6_3(X22,X23,X24),k1_relset_1(X22,X23,X24))
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_1(esk7_3(X22,X23,X24))
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(esk7_3(X22,X23,X24),X22,X23)
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(esk7_3(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = k1_funct_1(X24,X27)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(X27,k1_relset_1(X22,X23,X24))
        | k1_funct_1(esk7_3(X22,X23,X24),X27) = o_1_1_funct_2(X23)
        | ~ r2_hidden(X27,X22)
        | ~ r2_hidden(o_1_1_funct_2(X23),X23)
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X22,X23,X24)),X23)
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s5_funct_2__e3_154_1_2__funct_2])])])])])])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X57,X58,X59] :
      ( ( v4_relat_1(X59,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( v5_relat_1(X59,X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_24,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | v1_relat_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( v1_funct_1(esk7_3(X1,X2,X3))
    | ~ r2_hidden(esk6_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(k1_funct_1(X3,esk6_3(X1,X2,X3)),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v5_relat_1(X32,X30)
      | ~ v1_funct_1(X32)
      | ~ r2_hidden(X31,k1_relat_1(X32))
      | r2_hidden(k1_funct_1(X32,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_partfun1])])).

cnf(c_0_29,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_funct_2(esk7_3(X1,X2,X3),X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(k1_funct_1(X3,esk6_3(X1,X2,X3)),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_1(X1),k1_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk6_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(k1_funct_1(X3,esk6_3(X1,X2,X3)),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_22]),c_0_27])])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk7_3(esk1_0,esk2_0,esk3_0),esk1_0,esk2_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_22]),c_0_27])])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_40,plain,
    ( k1_funct_1(esk7_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(esk6_3(X2,X3,X4),k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(k1_funct_1(X4,esk6_3(X2,X3,X4)),X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_1(X1),k1_relat_1(esk3_0))
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_22]),c_0_27])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk7_3(esk1_0,esk2_0,esk3_0),esk1_0,esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_36]),c_0_37]),c_0_27])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk6_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(o_1_1_funct_2(X2),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,plain,
    ( v1_funct_1(esk7_3(X1,X2,X3))
    | r2_hidden(esk6_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(o_1_1_funct_2(X2),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( v1_funct_2(esk7_3(X1,X2,X3),X1,X2)
    | r2_hidden(esk6_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(o_1_1_funct_2(X2),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_22]),c_0_27])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])).

fof(c_0_51,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k1_relset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),k1_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

fof(c_0_53,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(X1,esk4_1(X1)) != k1_funct_1(esk3_0,esk4_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_22]),c_0_27])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_22]),c_0_27])]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk7_3(esk1_0,esk2_0,esk3_0),esk1_0,esk2_0)
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_26]),c_0_22]),c_0_27])]),c_0_44])).

cnf(c_0_58,plain,
    ( k1_funct_1(esk7_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | r2_hidden(esk6_3(X2,X3,X4),k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(o_1_1_funct_2(X3),X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_36]),c_0_37]),c_0_27])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),k1_relat_1(esk3_0))
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_35]),c_0_36]),c_0_37]),c_0_27])])).

fof(c_0_61,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),k1_relat_1(esk3_0))
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0))
    | k1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0),esk4_1(esk7_3(esk1_0,esk2_0,esk3_0))) != k1_funct_1(esk3_0,esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)))
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_26]),c_0_26]),c_0_27])]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),k1_relat_1(esk3_0))
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_55]),c_0_56]),c_0_57]),c_0_60])).

fof(c_0_68,plain,(
    ! [X48,X49,X50] :
      ( ( v1_funct_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v1_partfun1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v1_funct_2(X50,X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_partfun1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_69,plain,(
    ! [X51,X52,X53] :
      ( ~ v1_xboole_0(X51)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | v1_partfun1(X53,X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_26]),c_0_22])])).

fof(c_0_72,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(k1_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(esk7_3(esk1_0,esk2_0,esk3_0),esk4_1(esk7_3(esk1_0,esk2_0,esk3_0))) != k1_funct_1(esk3_0,esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0))
    | ~ r2_hidden(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),esk1_0)
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_27])])).

cnf(c_0_79,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),k1_relat_1(esk3_0))
    | ~ r2_hidden(esk6_3(esk1_0,esk2_0,esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_35]),c_0_36]),c_0_37]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk3_0))
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_74,c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r2_hidden(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),esk1_0)
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_66]),c_0_76]),c_0_67])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_partfun1(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_22]),c_0_27])]),c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( v1_partfun1(esk3_0,esk1_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk3_0))
    | m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),k1_relat_1(esk3_0))
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_55]),c_0_56]),c_0_57]),c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk3_0))
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_55]),c_0_56]),c_0_57]),c_0_64])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),esk1_0)
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_35]),c_0_36]),c_0_37]),c_0_27])]),c_0_76])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_3(esk1_0,esk2_0,esk3_0)),esk1_0)
    | ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

fof(c_0_93,plain,(
    ! [X16] : m1_subset_1(o_1_1_funct_2(X16),X16) ),
    inference(variable_rename,[status(thm)],[dt_o_1_1_funct_2])).

fof(c_0_94,plain,(
    ! [X43] :
      ( ~ v1_xboole_0(X43)
      | X43 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(o_1_1_funct_2(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_81]),c_0_91]),c_0_92])).

cnf(c_0_96,plain,
    ( m1_subset_1(o_1_1_funct_2(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_81]),c_0_96])])).

cnf(c_0_99,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_100,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_102,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_103,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_103]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
